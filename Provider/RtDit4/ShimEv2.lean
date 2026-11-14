-- (H-P13 → Release): the shim slot's data-event tails (s3 STP / s7 LDP: records
-- dataRecs spec (ofNat p.sp) true/false 16, Memory's MemTailE tails over prem_shimStp/Ldp) and E17
-- (TranslationAgrees) at a ShimInv state.
import RtDit4.ShimEv
import Bridge.CruxGenGuarded.E17Run
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts HeapV2StepCerts.MemNext
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace RtDit.ShimEv
open RtDit RtDit.Shim

section
variable {real : Type} [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {pbase : Nat} {table : Nat → Prop}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    {base : BitVec 64} {offset : Nat → BitVec 64} {bud : Nat} {k : Nat} {budget : Nat} {x : NativeState}

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.ShimEv.tail_stpE"
  (← IO.getStderr).flush

theorem tail_stpE
    (inv : RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
      scope image loadBase base offset bud k x)
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (spX : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp) (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table) x final budget →
    ∃ fin, nativeTail real x (NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7) enc0 final = .ok () fin ∧
      ∃ D : Array Event, fin.events = final.events ++ D ∧
        D.toList.map ArmCertCTOrdered.OrderedEventV2.record =
          HeapV2StepCerts.DataRecs.dataRecs spec (BitVec.ofNat 64 p.sp) true 16 := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have sysF : SysEq2 x.regs final.regs := EntryBranchPins.sysEq2_symm _ _ f.input.sys
  have spF : final.regs.SP_EL0 = BitVec.ofNat 64 p.sp := by
    rw [hregs, ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ x (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact spX
  have post2F := HeapV2StepCerts.MemConfigFrame.post2 sysF.feat sysF.el sysF.nrw sysF.scr sysF.hcr sysF.sctlr sysF.spe inv.post2
  have modeF := HeapV2StepCerts.MemConfigFrame.mode sysF.feat sysF.el sysF.scr sysF.hcr inv.mode
  have debugF := HeapV2StepCerts.MemConfigFrame.debug sysF.mdscr sysF.hde inv.debug
  have featF : final.regs.FeatureImpl[7] = true ∧ final.regs.FeatureImpl[3] = false ∧
      final.regs.FeatureImpl[227] = false ∧ final.regs.FeatureImpl[111] = true := by
    rw [sysF.feat]; exact inv.feat
  have dcacheF := HeapV2StepCerts.MemConfigFrame.dcache sysF.sctlr inv.dcache
  have hva : ArmCertMem.LdpEval.ldpAddr final 0#7 = BitVec.ofNat 64 p.sp :=
    (RtShim.SlotPrem.shim_addr final).trans spF
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
    RtShim.SlotPrem.prem_shimStp final f.closed static post2F spF spAligned
  obtain ⟨_, _, fin, _, delta, _, run, _, _, _, _, _, _, ev, _, recs, _⟩ :=
    HeapV2StepCerts.MemTailE.mem_tailD_Stp real spec config rows mapping x final enc0 0#7 9#5 30#5 (by decide)
      (by decide) (by decide +kernel) f.pins f.input f.guard budget f.quiet f.it f.ss f.current perAcc modeF debugF
      post2F featF.1 featF.2.1 featF.2.2.1 featF.2.2.2 dcacheF hsp hal pa mapped mmio outside (fun _ => True)
      (fun _ _ => trivial) (by rw [f.mem]; exact inv.raw)
      (fun acc sh => by rw [hostHAFT_eq sysF]; exact inv.noUpd true acc sh)
  exact ⟨fin, run, delta, ev, by rw [recs nodup, hva]⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.ShimEv.tail_ldpE"
  (← IO.getStderr).flush

theorem tail_ldpE
    (inv : RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
      scope image loadBase base offset bud k x)
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (present : RtShim.SlotPrem.ShimSlotPresent p mapping x)
    (spX : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp) (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table) x final budget →
    ∃ fin, nativeTail real x (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7) enc0 final = .ok () fin ∧
      ∃ D : Array Event, fin.events = final.events ++ D ∧
        D.toList.map ArmCertCTOrdered.OrderedEventV2.record =
          HeapV2StepCerts.DataRecs.dataRecs spec (BitVec.ofNat 64 p.sp) false 16 := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have sysF : SysEq2 x.regs final.regs := EntryBranchPins.sysEq2_symm _ _ f.input.sys
  have spF : final.regs.SP_EL0 = BitVec.ofNat 64 p.sp := by
    rw [hregs, ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ x (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact spX
  have post2F := HeapV2StepCerts.MemConfigFrame.post2 sysF.feat sysF.el sysF.nrw sysF.scr sysF.hcr sysF.sctlr sysF.spe inv.post2
  have modeF := HeapV2StepCerts.MemConfigFrame.mode sysF.feat sysF.el sysF.scr sysF.hcr inv.mode
  have debugF := HeapV2StepCerts.MemConfigFrame.debug sysF.mdscr sysF.hde inv.debug
  have featF : final.regs.FeatureImpl[7] = true ∧ final.regs.FeatureImpl[3] = false ∧
      final.regs.FeatureImpl[227] = false ∧ final.regs.FeatureImpl[111] = true := by
    rw [sysF.feat]; exact inv.feat
  have dcacheF := HeapV2StepCerts.MemConfigFrame.dcache sysF.sctlr inv.dcache
  have hva : ArmCertMem.LdpEval.ldpAddr final 0#7 = BitVec.ofNat 64 p.sp :=
    (RtShim.SlotPrem.shim_addr final).trans spF
  have presentF : RtShim.SlotPrem.ShimSlotPresent p mapping final := fun n hn i hi => by
    rw [f.mem]; exact present n hn i hi
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    RtShim.SlotPrem.prem_shimLdp final f.closed static presentF spF spAligned
  obtain ⟨_, _, fin, _, delta, _, run, _, _, _, _, _, _, ev, _, recs, _⟩ :=
    HeapV2StepCerts.MemTailE.mem_tailD_Ldp real spec config rows mapping x final enc0 0#7 9#5 30#5 (by decide)
      (by decide) (by decide) (by decide +kernel) f.pins f.input f.guard budget f.quiet f.it f.ss f.current perAcc
      modeF debugF post2F featF.1 featF.2.1 featF.2.2.1 featF.2.2.2 dcacheF hsp hal pa mapped mmio data bytes
      (fun _ => False) (by rw [f.mem]; exact inv.raw)
      (fun acc sh => by rw [hostHAFT_eq sysF]; exact inv.noUpd false acc sh)
  exact ⟨fin, run, delta, ev, by rw [recs nodup, hva]⟩
end

/-- Closed membership at a state from its pre-fetch view (beforeFetchState only touches fetch bookkeeping). -/
theorem closed_of_before {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} (x : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState x)) :
    ClosedMembershipAt spec config rows mapping m x := by
  refine closed_of_fields closed rfl ?_ ?_ rfl ?_ rfl ?_
  all_goals simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]

/-- E17 at a ShimInv state. -/
theorem e17_of_shimInv {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    {base : BitVec 64} {offset : Nat → BitVec 64} {budget k : Nat} {x : NativeState}
    (agrees : ConsumerMapAgrees spec mapping m)
    (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x) :
    ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m x := by
  refine translation_agrees_along spec config rows mapping m (· = 0) (fun _ => x) agrees ?_ 0 rfl
  intro n _
  obtain ⟨cur, mode, f4, debug, spe⟩ := E17StateFacts.state_facts (spec := spec) (config := config) (rows := rows) x
    (NativeEntryTail.EntryPins.of_scalar x inv.v2.v1.pins) inv.v2.v1.features inv.v2.v1.debug inv.v2.v1.current
  exact ⟨cur, mode, f4, debug, spe, closed_of_before x inv.v2.closed⟩

#print axioms tail_stpE
#print axioms tail_ldpE
#print axioms closed_of_before
#print axioms e17_of_shimInv
end RtDit.ShimEv
