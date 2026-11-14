-- Actual saved-pair restore, stack adjustment, DIT restore and caller RET.
import DefaultHeapShimControl
import DefaultHeapShimEffects
import DefaultHeapShimMem
import RtShimG.RtDit6_ShimChain
import DefaultHeapShimClass
import DefaultHeapShimProfiles
import DefaultHeapShimFetch

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts RtDit RtDit.Shim RtDit.Release
open ArmBridge.CruxGenGuarded.Release (shimMap)
open ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts.E17General RtDit.Window RtDit.ShimEv
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapShimFactory

theorem epilogue (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue) (e saved : NativeState)
    (room : 369 ≤ budget) (page : base.toNat % 4096 = 0)
    (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (straight : ∀ j, 365 ≤ j → j ≤ 367 → offS (j + 1) = offS j + 4#64)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)
    (inv365 : DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 365 catalogue (stateAt real e 365))
    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (prefixControl : RtPremC.CtlRel spec e (stateAt real e 365))
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)
    (offPre : ∀ j, j ≤ 6 → offS j = Release.shimPC j)
    (offPost : ∀ j, 365 ≤ j → j ≤ 368 → offS j = Release.shimPC (j - 358))
    (rows365 : NativeMteTagCheck.TagStatusRows (stateAt real e 365) ((stateAt real e 365).choiceOcc.getD 1354 0) 1)
    (sp365 : (stateAt real e 365).regs.SP_EL0 = BitVec.ofNat 64 pins.sp)
    (slot365 : SlotHas pins mapping (ArmCertMem.StpEval.stpData saved 9#5 30#5) (stateAt real e 365))

    (low : saved.regs.gpr[30].toNat < 2 ^ 55)
    (target : saved.regs.gpr[30] = base + offS 369) :
    (∀ j, 365 ≤ j → j ≤ 368 → modelStep real (stateAt real e j) = .ok () (stateAt real e (j + 1))) ∧
    DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 369 catalogue (stateAt real e 369) ∧
    (stateAt real e 369).regs.gpr[30] = saved.regs.gpr[30] ∧
    (stateAt real e 369).regs.gpr[9] = saved.regs.gpr[9] ∧
    (stateAt real e 369).regs.SP_EL0 = (stateAt real e 365).regs.SP_EL0 + BitVec.ofInt 64 16 ∧
    (∀ a : Nat, (stateAt real e 369).mem[a]? = (stateAt real e 365).mem[a]?) ∧
    (stateAt real e 369).regs.PSTATE.DIT = saved.regs.gpr[9].extractLsb 24 24 ∧
    (∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 →
      (stateAt real e 369).regs.gpr[i.val] = (stateAt real e 365).regs.gpr[i.val]) ∧
    RtPremC.CtlRel spec (stateAt real e 365) (stateAt real e 369) ∧
    (∃ draws, NativeMteTagCheck.ChoiceDelta (stateAt real e 365) (stateAt real e 369) draws ∧ draws ≤ 1) := by
  let fetches := DefaultHeapShimFetch.of_static real spec config rows mapping pins scope image loadBase
    base offS budget catalogue shimStatic himage hload offPre offPost
  have ob365 := fetches.ob365 _ inv365
  have tail8 := DefaultHeapShimChoice.tail8 real (stateAt real e 366)
  have add8 := NativeShimTails.add8
  have keep8all := NativeShimTails.keep8all
  have choice8 := DefaultHeapShimChoice.add_sp real (stateAt real e 366)
  have present365 : RtShim.SlotPrem.ShimSlotPresent pins mapping (stateAt real e 365) := by
    intro n hn i hi
    rw [slot365 n hn i hi]
    rfl
  obtain ⟨f, r365, i366, h366, wo5, _, pay, _, _, _, _, _, ctl365, draws365, delta365, bound365⟩ :=
    DefaultHeapShimMem.shim_mem_step real spec config rows mapping (shimMap spec mapping base pins) scope image loadBase separated
      base offS budget pins 365 catalogue (by omega) page (aligned 365) _ inv365 rows365 present365 sp365
      (fun _ => False) (fun _ _ _ _ h => h) (DefaultHeapShimMem.LoadPay pins mapping 9#5 30#5)
      (fun _ _ _ hm hp => DefaultHeapShimMem.load_pay_of_fetch hm hp) _ nodup _ _ _ _ (by decide)
      (DefaultHeapShimMem.shim_ldp real spec config rows mapping static spAligned 9#5 30#5
        (by decide) (by decide) (by decide) (by decide) catalogue _)
      (next_placed inv365.v1.pc (straight 365 (by omega) (by omega))) ob365
  have e366 : stateAt real e 366 = f := stateAt_succ_of r365
  rw [← e366] at i366 h366 wo5 pay r365 ctl365 delta365
  obtain ⟨pa, facts⟩ := static
  have restored := pay pa.toNat facts.mapped (ArmCertMem.StpEval.stpData saved 9#5 30#5)
    (slot365 pa.toNat facts.mapped)
  simp only [show (RegBind.rk (30#5)).val = 30 from by decide,
    show (RegBind.rk (9#5)).val = 9 from by decide] at restored
  have lr366 : (stateAt real e 366).regs.gpr[30] = saved.regs.gpr[30] := by
    rw [restored.1, ldpHi_stpData]
  have x9366 : (stateAt real e 366).regs.gpr[9] = saved.regs.gpr[9] := by
    rw [restored.2, ldpLo_stpData]
  have ob8 := fetches.ob8 _ i366
  obtain ⟨f, r366, i367, h367, m367, _, ctl366, delta366⟩ :=
    DefaultHeapShimClass.classStep real spec config rows mapping (shimMap spec mapping base pins) scope image loadBase separated base offS budget 366 catalogue
      (by omega) page (aligned 366) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i366
      (classE_toV tail8) (next_placed i366.v1.pc (straight 366 (by omega) (by omega))) ob8 choice8
  have e367 : stateAt real e 367 = f := stateAt_succ_of r366
  rw [← e367] at i367 h367 m367 r366 ctl366 delta366
  have prof9 := DefaultHeapShimProfiles.msr mrsEntry isbEntry
    (DefaultHeapShimProfiles.features ((prefixControl.trans ctl365).trans ctl366))
  have choice9 := DefaultHeapShimChoice.msr real (stateAt real e 367) prof9
  have ob9 := fetches.ob9 _ i367
  obtain ⟨f, r367, i368, h368, m368, _, ctl367, delta367⟩ :=
    DefaultHeapShimClass.classStep real spec config rows mapping (shimMap spec mapping base pins) scope image loadBase separated base offS budget 367 catalogue
      (by omega) page (aligned 367) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i367
      (NativeShimTails.msrDit9_tailVAt real _ prof9)
      (next_placed i367.v1.pc (straight 367 (by omega) (by omega))) ob9 choice9
  have e368 : stateAt real e 368 = f := stateAt_succ_of r367
  rw [← e368] at i368 h368 m368 r367 ctl367 delta367
  have lr368 : (stateAt real e 368).regs.gpr[30] = saved.regs.gpr[30] := by
    rw [RtSaved.kept_reg h368 ⟨30, by decide⟩ rfl,
      RtSaved.kept_reg h367 ⟨30, by decide⟩ (keep8all _), lr366]
  have x9368 : (stateAt real e 368).regs.gpr[9] = saved.regs.gpr[9] := by
    rw [RtSaved.kept_reg h368 ⟨9, by decide⟩ rfl,
      RtSaved.kept_reg h367 ⟨9, by decide⟩ (keep8all _), x9366]
  have ob10 := fetches.ob10 _ i368
  obtain ⟨f, r368, i369, g369, sp369, m369, dit369, _, _, ctl368, delta368⟩ :=
    DefaultHeapShimControl.shim_ret real spec config rows mapping (shimMap spec mapping base pins) scope image loadBase separated
      base offS budget 368 catalogue (by omega) page (aligned 368) nodup _ i368
      (by rw [lr368]; exact low) (lr368.trans target) ob10
  have e369 : stateAt real e 369 = f := stateAt_succ_of r368
  rw [← e369] at i369 g369 sp369 m369 dit369 r368 ctl368 delta368
  have sp366 : (stateAt real e 366).regs.SP_EL0 = (stateAt real e 365).regs.SP_EL0 := h366 .sp
  have sp367 : (stateAt real e 367).regs.SP_EL0 = (stateAt real e 366).regs.SP_EL0 + BitVec.ofInt 64 16 := by
    have h := h367 .sp
    rw [add8] at h
    exact h
  have dit368 : (stateAt real e 368).regs.PSTATE.DIT = saved.regs.gpr[9].extractLsb 24 24 := by
    obtain ⟨f, run, dit, _⟩ := DefaultHeapShimEffects.shim_msr9 real spec config rows mapping (shimMap spec mapping base pins) scope image loadBase
      base offS budget 367 catalogue (by omega) page (aligned 367) _ i367 prof9 ob9
    have same := ok_inj (real := real) run r367
    subst f
    rw [dit, RtSaved.kept_reg h367 ⟨9, by decide⟩ (keep8all _), x9366]
  have allControl := ((ctl365.trans ctl366).trans ctl367).trans ctl368
  have allChoice : NativeMteTagCheck.ChoiceDelta (stateAt real e 365) (stateAt real e 369) draws365 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans delta365 delta366) delta367) delta368
  refine ⟨?_, i369, by rw [g369, lr368], by rw [g369, x9368], ?_, ?_, dit369.trans dit368, ?_, allControl, ⟨draws365, allChoice, bound365⟩⟩
  · intro j lo hi
    rcases (show j = 365 ∨ j = 366 ∨ j = 367 ∨ j = 368 by omega) with rfl | rfl | rfl | rfl
    · exact r365
    · exact r366
    · exact r367
    · exact r368
  · rw [sp369, show (stateAt real e 368).regs.SP_EL0 = (stateAt real e 367).regs.SP_EL0 from h368 .sp,
      sp367, sp366]
  · intro a
    rw [m369, m368, m367, wo5 a (by simp)]
  · intro i n9 n30
    have keepAll : ∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 →
        RegBind.updOf (RegBind.updLdp 9#5 30#5) (.x i) = .keep := by decide
    have keepLdp := keepAll i n9 n30
    rw [g369, RtSaved.kept_reg h368 i rfl, RtSaved.kept_reg h367 i (keep8all i),
      RtSaved.kept_reg h366 i keepLdp]


#print axioms epilogue
end ReleaseProfile.DefaultHeapShimFactory
