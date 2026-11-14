-- rich-v6 (B1 (a)): LDP payload for both halves (X[Rt] = ldpLo, X[Rt2] = ldpHi).
import HeapV2StepCerts.MemStepV3
import RtSaved.SlotCore
import RtSaved.MemFacts
import RtS3.MemTailP2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.HeapV2Compose ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ClosedChain
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace RtSaved3.MemFacts2
open RtSaved.MemFacts
open HeapV2StepCerts HeapV2StepCerts.MemNext HeapV2StepCerts.RegBind HeapV2StepCerts.C3

/-- LDP payload for both halves: X[Rt2] := ldpHi, X[Rt] := ldpLo of the 128-bit value at the access's PA in `f`. -/
def LdpPay2 (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (e : Nat × Nat × Int × Nat × Bool)
    (Rt Rt2 : BitVec 5) (f fin : NativeState) : Prop :=
  ∀ n, mapping (HeapV2E17.dataVA p e) = some n → ∀ d : BitVec 128,
    (∀ i < 16, f.mem[n + i]? = some (d.extractLsb' (8 * i) 8)) →
    fin.regs.gpr[(rk Rt2).val] = ArmCertMem.LdpEval.ldpHi d ∧ fin.regs.gpr[(rk Rt).val] = ArmCertMem.LdpEval.ldpLo d

theorem LdpPay2.transport {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    {e : Nat × Nat × Int × Nat × Bool} {Rt Rt2 : BitVec 5} {f s fin : NativeState}
    (mem : f.mem = s.mem) (h : LdpPay2 p mapping e Rt Rt2 f fin) : LdpPay2 p mapping e Rt Rt2 s fin := by
  intro n hn d hd; exact h n hn d (fun i hi => by rw [mem]; exact hd i hi)

theorem LdpPay2.toPay {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    {e : Nat × Nat × Int × Nat × Bool} {Rt Rt2 : BitVec 5} {s fin : NativeState}
    (h : LdpPay2 p mapping e Rt Rt2 s fin) : LdpPay p mapping e Rt2 s fin :=
  fun n hn d hd => (h n hn d hd).1

theorem memVP_Ldp2 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdp Rt Rt2) (source : NativeState) :
    MemTailVPAt real spec config rows (Ctx spec config rows mapping p base table k) (fun _ => False)
      (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) NativeEntryBodyMem.Ldp.writes 611 source
      (source.regs._PC + 4#64) (upds k) (LdpPay2 p mapping e Rt Rt2) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    prem_Ldp fetched ctx.closed static ctx.present pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW, pay, payLo⟩ :=
    RtSaved3.MemTailP2.mem_tailP2_Ldp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio data bytes (fun _ => False) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  refine ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, ?_⟩
  intro n hn d hd
  rw [← hva, mapped] at hn
  obtain rfl : pa.toNat = n := Option.some.inj hn
  have same : data = d := RtSaved.bytes_ext (fun i hi => Option.some.inj ((bytes i hi).symm.trans (hd i hi)))
  exact ⟨by rw [pay, same], by rw [payLo, same]⟩

#print axioms memVP_Ldp2
#print axioms LdpPay2.transport
end RtSaved3.MemFacts2
