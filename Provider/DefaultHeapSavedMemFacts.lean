-- Heap body memory geometry and real MTE2 tails, using current checked controls.
import DefaultHeapMemFacts
import DefaultHeapSavedTail
import RtS3.MemFacts2

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.HeapV2Compose
open HeapV2StepCerts HeapV2StepCerts.MemFactsE HeapV2StepCerts.RegBind HeapV2StepCerts.C3
open NativeMteTagCheck
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapSavedMemFacts
open ReleaseProfile.DefaultHeapMemFacts

theorem memEP_Stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) (hupd : upds k = []) (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapEntryMem.MemTailDefaultAt real spec config rows (CurrentCtx spec config rows mapping p base table k catalogue 1) (RtSaved.accPA p mapping e)
      (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) NativeEntryBodyMem.Stp.writes 617 source
      (source.regs._PC + 4#64) (upds k) (RtSaved.MemFacts.StpPay p mapping e Rt Rt2)
      (DataRecs.dataRecs spec (HeapV2E17.dataVA p e) e.2.2.2.2 e.2.2.2.1) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hvaE : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
    prem_Stp fetched ctx.closed static pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  have inD : ∀ i < 16, RtSaved.accPA p mapping e (pa.toNat + i) := fun i hi =>
    Or.inl ⟨pa.toNat, hva ▸ mapped, by omega, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg, gic, pc, np, keep, ⟨holds, inW, pay⟩, choice, bound⟩ :=
    ReleaseProfile.DefaultHeapSavedTail.mem_tailP_Stp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio outside (RtSaved.accPA p mapping e) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  refine ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, ?_, ⟨delta, ev, fun nd => by rw [(recs nd), hvaE, hw, hsize]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩
  intro n hn i hi
  rw [← hvaE, mapped] at hn
  obtain rfl : pa.toNat = n := Option.some.inj hn
  rw [pay i hi]
  exact congrArg some (RtSaved.slotByte_stp _ _ i)

theorem memEP_Ldp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdp Rt Rt2) (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapEntryMem.MemTailDefaultAt real spec config rows (CurrentCtx spec config rows mapping p base table k catalogue 1) (fun _ => False)
      (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) NativeEntryBodyMem.Ldp.writes 611 source
      (source.regs._PC + 4#64) (upds k) (RtSaved3.MemFacts2.LdpPay2 p mapping e Rt Rt2)
      (DataRecs.dataRecs spec (HeapV2E17.dataVA p e) e.2.2.2.2 e.2.2.2.1) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hvaE : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    prem_Ldp fetched ctx.closed static ctx.present pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg, gic, pc, np, keep, ⟨holds, inW, pay, payLo⟩, choice, bound⟩ :=
    ReleaseProfile.DefaultHeapSavedTail.mem_tailP_Ldp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio data bytes (fun _ => False) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  refine ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, ?_, ⟨delta, ev, fun nd => by rw [(recs nd), hvaE, hw, hsize]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩
  intro n hn d hd
  rw [← hvaE, mapped] at hn
  obtain rfl : pa.toNat = n := Option.some.inj hn
  have same : data = d := RtSaved.bytes_ext (fun i hi => Option.some.inj ((bytes i hi).symm.trans (hd i hi)))
  rw [← same]
  exact ⟨pay, payLo⟩

#print axioms memEP_Stp
#print axioms memEP_Ldp
end ReleaseProfile.DefaultHeapSavedMemFacts
