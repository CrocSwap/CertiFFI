-- (lrSaved,): the memory-step facts LrField's carries consume.
-- memVD_<K>: Memory's memV_<K> (MemStepV3.lean) with the exact write set D := RtSaved.accPA p mapping e
-- for stores and D := ∅ for loads (instead of the all-plan dataBytes, which contains the slot).
-- memVP_Stp / memVP_Ldp: the same plus the payload (MemTailVPAt = MemTailVAt ∧ Pay fetched fin).
-- Transports to the step's source state and the two value-step glues into LrField.
import HeapV2StepCerts.MemStepV3
import RtSaved.SlotCore
import RtSaved.MemTailP
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
namespace RtSaved.MemFacts
open HeapV2StepCerts HeapV2StepCerts.MemNext HeapV2StepCerts.RegBind HeapV2StepCerts.C3

/-- STP payload: the bytes at the access's PA are (X[Rt], X[Rt2]) of `f`, little-endian. -/
def StpPay (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (e : Nat × Nat × Int × Nat × Bool)
    (Rt Rt2 : BitVec 5) (f fin : NativeState) : Prop :=
  ∀ n, mapping (HeapV2E17.dataVA p e) = some n → ∀ i < 16,
    fin.mem[n + i]? = some (RtSaved.slotByte (f.regs.gpr[(rk Rt).val]) (f.regs.gpr[(rk Rt2).val]) i)

/-- LDP payload: X[Rt2] := the high half of whatever 128-bit value sits at the access's PA in `f`. -/
def LdpPay (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (e : Nat × Nat × Int × Nat × Bool)
    (Rt2 : BitVec 5) (f fin : NativeState) : Prop :=
  ∀ n, mapping (HeapV2E17.dataVA p e) = some n → ∀ d : BitVec 128,
    (∀ i < 16, f.mem[n + i]? = some (d.extractLsb' (8 * i) 8)) →
    fin.regs.gpr[(rk Rt2).val] = ArmCertMem.LdpEval.ldpHi d

/-- MemTailVAt with one more exported fact `Pay fetched fin`. -/
def MemTailVPAt (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (Ctx : NativeState → Prop) (D : Nat → Prop)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (source : NativeState) (next : BitVec 64)
    (us : List (RegBind.Reg × RegBind.Upd)) (Pay : NativeState → NativeState → Prop) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched → MetadataGuard fetched →
    HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    CurrentS1At spec config rows fetched → Ctx fetched →
    ∃ (sp a fin : NativeState) (written : Nat → Prop),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame writes (actionState w sp K) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      WritesOnly written (fun x => fetched.mem[x]?) (fun x => fin.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ x, written x → D x) ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = next ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      (∀ x : Nat, (fetched.mem[x]?).isSome → (fin.mem[x]?).isSome) ∧
      RegBind.Holds us fetched fin ∧ Pay fetched fin

/-- Forgetting the payload gives Memory's MemTailVAt (so plan_step3_mem still applies). -/
theorem MemTailVPAt.toV {real : Type} [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {Ctx : NativeState → Prop} {D : Nat → Prop}
    {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {source : NativeState} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)} {Pay : NativeState → NativeState → Prop}
    (h : MemTailVPAt real spec config rows Ctx D w writes K source next us Pay) :
    MemTailVAt real spec config rows Ctx D w writes K source next us := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨sp, a, fin, written, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, _⟩ :=
    h fetched enc0 budget pins input guard quiet it ss current ctx
  exact ⟨sp, a, fin, written, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem memVD_Ldrb (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm9 : BitVec 9) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) 31 12 == 879088#20) = false)
    {r : Reg} (hat : accessAt e.1 = some (r, 0)) (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdrb Rn Rt imm9) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (fun _ => False)
      (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) NativeEntryBodyMem.Ldrb.writes 631 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  obtain ⟨perAcc, pa, mapped, mmio, outside, v, byte⟩ :=
    prem_Ldrb fetched ctx.closed static ctx.present member ctx.regBind Rn hat hsize hw
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inD⟩ :=
    MemTail.mem_tailD_Ldrb real spec config rows mapping source fetched enc0 imm9 Rn Rt hRn hRt hRnt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.dcache pa mapped mmio v byte outside (fun _ => False) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inD, gic, pc, np, keep, holds⟩

theorem memVD_Ldp (real : Type) [Sail.SailReal real]
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
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (fun _ => False)
      (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) NativeEntryBodyMem.Ldp.writes 611 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    prem_Ldp fetched ctx.closed static ctx.present pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Ldp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio data bytes (fun _ => False) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memVD_Ldp8 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} {r : Reg} (hat : accessAt e.1 = some (r, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdp Rt Rt2) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (fun _ => False)
      (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) NativeEntryBodyMem.Ldp8.writes 611 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  obtain ⟨perAcc, h8, pa1, pa2, mapped1, mapped2, contiguous, mmio1, mmio2, data, bytes1, bytes2⟩ :=
    prem_Ldp8 fetched ctx.closed static ctx.present pinAligned member ctx.regBind Rn imm7 hat himm hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Ldp8 real spec config rows mapping source fetched enc0 imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache h8 pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2 data bytes1 bytes2
      (fun _ => False) ctx.raw (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memVD_Strb (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm9 : BitVec 9) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Strb.selected Rt Rn imm9) 31 12 == 879088#20) = false)
    {r : Reg} (hat : accessAt e.1 = some (r, 0)) (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = true) (hupd : upds k = updStrb Rn imm9) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (RtSaved.accPA p mapping e)
      (NativeEntryBodyDispatch.Strb.selected Rt Rn imm9) NativeEntryBodyMem.Strb.writes 649 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  have hva := base_va member ctx.regBind hat
  obtain ⟨perAcc, pa, mapped, mmio, outside⟩ :=
    prem_Strb fetched ctx.closed static ctx.post2 member ctx.regBind Rn hat hsize hw
  have inD : RtSaved.accPA p mapping e pa.toNat :=
    Or.inl ⟨pa.toNat, hva ▸ mapped, Nat.le_refl _, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Strb real spec config rows mapping source fetched enc0 imm9 Rn Rt hRn hRt hRnt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 pa mapped mmio outside (RtSaved.accPA p mapping e) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memVD_Stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) (hupd : upds k = []) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (RtSaved.accPA p mapping e)
      (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) NativeEntryBodyMem.Stp.writes 617 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
    prem_Stp fetched ctx.closed static ctx.post2 pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  have inD : ∀ i < 16, RtSaved.accPA p mapping e (pa.toNat + i) := fun i hi =>
    Or.inl ⟨pa.toNat, hva ▸ mapped, by omega, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Stp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio outside (RtSaved.accPA p mapping e) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memVD_Stp8 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} {r : Reg} (hat : accessAt e.1 = some (r, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) (hupd : upds k = []) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (RtSaved.accPA p mapping e)
      (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) NativeEntryBodyMem.Stp8.writes 617 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  have hva : MemClass.Stp8.pairAddr fetched Rn imm7 = HeapV2E17.dataVA p e :=
    pair8_va member ctx.regBind Rn imm7 hat himm
  obtain ⟨perAcc, preW, h8, pa1, pa2, mapped1, mapped2, contiguous, mmio1, mmio2, outside1, outside2⟩ :=
    prem_Stp8 fetched ctx.closed static ctx.post2 pinAligned member ctx.regBind Rn imm7 hat himm hoff.2 hsize hw
  have inD1 : ∀ i < 8, RtSaved.accPA p mapping e (pa1.toNat + i) := fun i hi =>
    Or.inl ⟨pa1.toNat, hva ▸ mapped1, by omega, by rw [hsize]; omega⟩
  have inD2 : ∀ i < 8, RtSaved.accPA p mapping e (pa2.toNat + i) := fun i hi =>
    Or.inr ⟨hsize, pa2.toNat, hva ▸ mapped2, by omega, by omega⟩
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Stp8 real spec config rows mapping source fetched enc0 imm7 Rn Rt Rt2 hRn hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc preW ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache h8 pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2 outside1 outside2
      (RtSaved.accPA p mapping e) inD1 inD2 ctx.raw (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memVP_Stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) (hupd : upds k = []) (source : NativeState) :
    MemTailVPAt real spec config rows (Ctx spec config rows mapping p base table k) (RtSaved.accPA p mapping e)
      (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) NativeEntryBodyMem.Stp.writes 617 source
      (source.regs._PC + 4#64) (upds k) (StpPay p mapping e Rt Rt2) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
    prem_Stp fetched ctx.closed static ctx.post2 pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  have inD : ∀ i < 16, RtSaved.accPA p mapping e (pa.toNat + i) := fun i hi =>
    Or.inl ⟨pa.toNat, hva ▸ mapped, by omega, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW, pay⟩ :=
    RtSaved.MemTailP.mem_tailP_Stp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio outside (RtSaved.accPA p mapping e) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  refine ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, ?_⟩
  intro n hn i hi
  rw [← hva, mapped] at hn
  obtain rfl : pa.toNat = n := Option.some.inj hn
  rw [pay i hi]
  exact congrArg some (RtSaved.slotByte_stp _ _ i)

theorem memVP_Ldp (real : Type) [Sail.SailReal real]
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
      (source.regs._PC + 4#64) (upds k) (LdpPay p mapping e Rt2) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    prem_Ldp fetched ctx.closed static ctx.present pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW, pay⟩ :=
    RtSaved.MemTailP.mem_tailP_Ldp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio data bytes (fun _ => False) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  refine ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, ?_⟩
  intro n hn d hd
  rw [← hva, mapped] at hn
  obtain rfl : pa.toNat = n := Option.some.inj hn
  have same : data = d := RtSaved.bytes_ext (fun i hi => Option.some.inj ((bytes i hi).symm.trans (hd i hi)))
  rw [pay, same]

/-- The fetch keeps GPRs: the STP payload restates over the step's source state. -/
theorem StpPay.transport {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    {e : Nat × Nat × Int × Nat × Bool} {Rt Rt2 : BitVec 5} {f s fin : NativeState}
    (gpr : f.regs.gpr = s.regs.gpr) (h : StpPay p mapping e Rt Rt2 f fin) : StpPay p mapping e Rt Rt2 s fin := by
  intro n hn i hi; rw [← gpr]; exact h n hn i hi

/-- The fetch keeps memory: the LDP payload restates over the step's source state. -/
theorem LdpPay.transport {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    {e : Nat × Nat × Int × Nat × Bool} {Rt2 : BitVec 5} {f s fin : NativeState}
    (mem : f.mem = s.mem) (h : LdpPay p mapping e Rt2 f fin) : LdpPay p mapping e Rt2 s fin := by
  intro n hn d hd; exact h n hn d (fun i hi => by rw [mem]; exact hd i hi)

/-- k = 11 (STP x19, x30, [sp, #48]) into LrField. -/
theorem field_stp11 {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {s fin : NativeState} (pay : StpPay p mapping RtSaved.slotEntry 19#5 30#5 s fin)
    (field : RtSaved.LrField p mapping v19 v30 11 s) : RtSaved.LrField p mapping v19 v30 12 fin :=
  RtSaved.carry_stp11 (fun n hn i hi => by
    have h := pay n hn i hi
    simp only [show (rk (19#5)).val = 19 by decide, show (rk (30#5)).val = 30 by decide] at h
    exact h) field

/-- k = 354 (LDP x19, x30, [sp, #48]) into LrField. -/
theorem field_ldp354 {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {s fin : NativeState} (mapped : ∃ n, mapping (RtSaved.slotVA p) = some n)
    (pay : LdpPay p mapping (354, 0, -16, 16, false) 30#5 s fin)
    (field : RtSaved.LrField p mapping v19 v30 354 s) : RtSaved.LrField p mapping v19 v30 355 fin :=
  RtSaved.carry_ldp354 mapped (fun n hn d hd => by
    have h := pay n hn d hd
    simp only [show (rk (30#5)).val = 30 by decide] at h
    exact h) field

/-- The slot is mapped (DataStatic's dataOK of the prologue STP access). -/
theorem slot_mapped {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {fp : Footprint}
    (static : DataStatic p mapping fp) : ∃ n, mapping (RtSaved.slotVA p) = some n := by
  have ok := List.all_eq_true.1 static RtSaved.slotEntry RtSaved.slot_entry_member
  unfold C3.dataOK at ok
  cases h : mapping (HeapV2E17.dataVA p RtSaved.slotEntry) with
  | none => rw [h] at ok; simp at ok
  | some n => exact ⟨n, h⟩

#print axioms memVD_Ldrb
#print axioms memVD_Ldp
#print axioms memVD_Ldp8
#print axioms memVD_Strb
#print axioms memVD_Stp
#print axioms memVD_Stp8
#print axioms memVP_Stp
#print axioms memVP_Ldp
#print axioms MemTailVPAt.toV
#print axioms StpPay.transport
#print axioms LdpPay.transport
#print axioms field_stp11
#print axioms field_ldp354
#print axioms slot_mapped
end RtSaved.MemFacts
