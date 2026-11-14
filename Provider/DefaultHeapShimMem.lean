-- Actual MTE2-on shim slot store and load, including their byte and register effects.
import DefaultHeapShimEntry
import DefaultHeapSavedTail
import RtShim2.ShimMem
import DefaultHeapMemFacts
import DefaultCurrent

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ClosedChain
open ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts HeapV2StepCerts.MemFactsE HeapV2StepCerts.MemNext HeapV2StepCerts.C3
open NativeMteTagCheck
open ArmCert.HookQuiet.V0 (HookQuiet)
open RtShim.SlotPrem
open RtShim2.ShimMem (slotBytes)

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapShimMem

abbrev SlotCtx {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (S : Nat × Nat × Int × Nat × Bool → Prop) (p : HeapV2E17.Pins) (base : Nat) (table : Nat → Prop) (catalogue : ControlCatalogue) :=
  DefaultHeapShimEntry.ShimCtx spec config rows mapping (HeapV2E17.consumerMapShim S p base mapping table) p catalogue 1

def StorePay (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (rt rt2 : BitVec 5)
    (s fin : NativeState) : Prop :=
  ∀ n, mapping (BitVec.ofNat 64 p.sp) = some n → ∀ i < 16,
    fin.mem[n + i]? = some (MemM1.MemWriteD4.wbyte (ArmCertMem.StpEval.stpData s rt rt2) i)

def LoadPay (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (rt rt2 : BitVec 5)
    (s fin : NativeState) : Prop :=
  ∀ n, mapping (BitVec.ofNat 64 p.sp) = some n → ∀ d : BitVec 128,
    (∀ i < 16, s.mem[n + i]? = some (d.extractLsb' (8 * i) 8)) →
    fin.regs.gpr[(RegBind.rk rt2).val] = ArmCertMem.LdpEval.ldpHi d ∧
    fin.regs.gpr[(RegBind.rk rt).val] = ArmCertMem.LdpEval.ldpLo d

#check "CURRENT_DECL shim_stp"
theorem shim_stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (aligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 0#7) 31 12 == 879088#20) = false)
    (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapShimEntry.MemTailDefaultAt real spec config rows (SlotCtx spec config rows mapping S p base table catalogue)
      (slotBytes p mapping) (NativeEntryBodyDispatch.Stp.selected Rt Rt2 0#7)
      NativeEntryBodyMem.Stp.writes 617 source (source.regs._PC + 4#64) []
      (StorePay p mapping Rt Rt2) (DataRecs.dataRecs spec (BitVec.ofNat 64 p.sp) true 16) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  have hva := (shim_addr fetched).trans ctx.spAt
  obtain ⟨pa, facts⟩ := static
  have mapped : mapping (ArmCertMem.LdpEval.ldpAddr fetched 0#7) = some pa.toNat := hva.symm ▸ facts.mapped
  have hsp : fetched.regs.SP_EL0.toNat % 16 = 0 := by rw [ctx.spAt]; exact aligned
  have hal : (ArmCertMem.LdpEval.ldpAddr fetched 0#7).toNat % 16 = 0 := by rw [hva]; exact aligned
  have inD : ∀ i < 16, slotBytes p mapping (pa.toNat + i) := fun i hi =>
    ⟨pa.toNat, facts.mapped, by omega, by omega⟩
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg,
      gic, pc, np, keep, ⟨holds, inW, pay⟩, choice, bound⟩ :=
    DefaultHeapSavedTail.mem_tailP_Stp real spec config rows mapping source fetched enc0 0#7 Rt Rt2 hRt hRt2 noEret
      pins input guard budget quiet it ss current (fun _ sh => access_of_closed_shim ctx.closed hva sh)
      ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1 ctx.feat.2.2.1 ctx.feat.2.2.2
      ctx.dcache hsp hal pa mapped facts.mmio facts.outside (slotBytes p mapping) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  refine ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds,
    ?_, ⟨delta, ev, fun nd => by rw [recs nd, hva]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩
  intro n hn i hi
  obtain rfl : pa.toNat = n := Option.some.inj (facts.mapped.symm.trans hn)
  exact pay i hi

#check "CURRENT_DECL shim_ldp"
theorem shim_ldp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (aligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (distinct : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 0#7) 31 12 == 879088#20) = false)
    (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapShimEntry.MemTailDefaultAt real spec config rows (SlotCtx spec config rows mapping S p base table catalogue)
      (fun _ => False) (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 0#7)
      NativeEntryBodyMem.Ldp.writes 611 source (source.regs._PC + 4#64) (RegBind.updLdp Rt Rt2)
      (LoadPay p mapping Rt Rt2) (DataRecs.dataRecs spec (BitVec.ofNat 64 p.sp) false 16) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  have hva := (shim_addr fetched).trans ctx.spAt
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    prem_shimLdp fetched ctx.closed static ctx.slot ctx.spAt aligned
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg,
      gic, pc, np, keep, ⟨holds, inW, hi, lo⟩, choice, bound⟩ :=
    DefaultHeapSavedTail.mem_tailP_Ldp real spec config rows mapping source fetched enc0 0#7 Rt Rt2 hRt hRt2 distinct noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows
      ctx.feat.1 ctx.feat.2.1 ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio
      data bytes (fun _ => False) ctx.raw (fun acc sh => ctx.noUpd false acc sh)
  refine ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds,
    ?_, ⟨delta, ev, fun nd => by rw [recs nd, hva]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩
  intro n hn d hd
  rw [← hva, mapped] at hn
  obtain rfl : pa.toNat = n := Option.some.inj hn
  have same : data = d := RtSaved.bytes_ext (fun i hi => Option.some.inj ((bytes i hi).symm.trans (hd i hi)))
  rw [← same]
  exact ⟨hi, lo⟩

#print axioms shim_stp
#print axioms shim_ldp

theorem store_pay_of_fetch {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    {rt rt2 : BitVec 5} {s f fin : NativeState}
    (gpr : f.regs.gpr = s.regs.gpr) (pay : StorePay p mapping rt rt2 f fin) :
    StorePay p mapping rt rt2 s fin := by
  intro n hn i hi
  have h := pay n hn i hi
  simpa only [ArmCertMem.StpEval.stpData, gpr] using h

theorem load_pay_of_fetch {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    {rt rt2 : BitVec 5} {s f fin : NativeState}
    (mem : f.mem = s.mem) (pay : LoadPay p mapping rt rt2 f fin) :
    LoadPay p mapping rt rt2 s fin := by
  intro n hn d hd
  exact pay n hn d (by rw [mem]; exact hd)

#check "CURRENT_DECL shim_mem_step"
theorem shim_mem_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat) (catalogue : ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (status : TagStatusRows x (x.choiceOcc.getD 1354 0) 1)
    (slot : ShimSlotPresent p mapping x) (spAt : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (Pay : NativeState → NativeState → Prop)
    (payT : ∀ f y, f.regs.gpr = x.regs.gpr → f.mem = x.mem → Pay f y → Pay x y)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (us : List (RegBind.Reg × RegBind.Upd))
    (noWriteDit : writes.dit = false)
    (tail : DefaultHeapShimEntry.MemTailDefaultAt real spec config rows (DefaultHeapShimEntry.ShimCtx spec config rows mapping m p catalogue 1)
      D w writes K x (x.regs._PC + 4#64) us Pay data 1)
    (target : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      RegBind.Holds us x fin ∧ (∀ a, ¬ D a → fin.mem[a]? = x.mem[a]?) ∧
      ShimSlotPresent p mapping fin ∧ Pay x fin ∧
      fin.regs._Z = x.regs._Z ∧ Flags.nzcv fin.regs = Flags.nzcv x.regs ∧
      StepEvents.EvShape spec mapping data x fin ∧ ChainInvV4.GcsFrame x fin ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.CtlRel spec x fin ∧
      ∃ draws, ChoiceDelta x fin draws ∧ draws ≤ 1 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, holds,
    ⟨written, wo, sep, inD⟩, keep, sys, pay, z, fl, ev, gcs, tco, dit, control, draws, choice, bound⟩ :=
    DefaultHeapShimEntry.entry_shim_mem real spec config rows mapping w writes K x inv.v1.pins (x.regs._PC + 4#64)
      (offset (k + 1)) us m p D Pay payT data catalogue 1 tail nodup inv.v1.gic inv.v1.features inv.v1.debug
      (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned target inv.v1.current inv.closed
      scope image loadBase inv.placed separated codeD inv.branch inv.raw inv.noUpd slot spAt
      inv.post inv.controls status inv.mode inv.debug inv.feat inv.dcache
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp,
    RawFetch.raw_writes inv.raw wo sep, ?_, postFrame sys inv.post,
    MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    MemConfigFrame.dcache sys.sctlr inv.dcache,
    DefaultActionControls.controls_of_sys inv.controls sys tco⟩,
    holds, fun a ha => wo a (fun hw => ha (inD a hw)), fun n hm i hi => keep _ (slot n hm i hi),
    pay, z, fl, ev, gcs, dit noWriteDit, control, draws, choice, bound⟩
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms shim_mem_step
end ReleaseProfile.DefaultHeapShimMem
