-- Actual saved-pair restore, stack adjustment, DIT restore and caller RET.
import DefaultHeapShimControl
import DefaultHeapShimEffects
import DefaultHeapShimMem
import RtShimG.RtDit6_ShimChain
import DefaultHeapShimClass
import DefaultHeapShimFactory
import DefaultHeapShimBody
import DefaultHeapDitRun
import DefaultHeapShimProfiles
import DefaultHeapShimFetch

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open CertiFFI.Prog.Generic.ModelRunView
open NativeMteTagCheck
open HeapV2StepCerts RtDit RtDit.Shim RtDit.Release
open ArmBridge.CruxGenGuarded.Release (shimPC shimMap)
open ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts.E17General RtDit.Window RtDit.ShimEv
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapShimFactory

theorem epilogue_dit_window (real : Type) [Sail.SailReal real]
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
    (∀ j, 365 ≤ j → j ≤ 367 →
      (stateAt real e j).regs.PSTATE.DIT = (stateAt real e 365).regs.PSTATE.DIT) ∧
    (stateAt real e 368).regs.PSTATE.DIT = saved.regs.gpr[9].extractLsb 24 24 ∧
    (stateAt real e 369).regs.PSTATE.DIT = saved.regs.gpr[9].extractLsb 24 24 := by
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
  obtain ⟨f, r365, i366, h366, wo5, _, pay, _, _, _, _, dit365, ctl365, draws365, delta365, bound365⟩ :=
    DefaultHeapShimMem.shim_mem_step real spec config rows mapping (shimMap spec mapping base pins) scope image loadBase separated
      base offS budget pins 365 catalogue (by omega) page (aligned 365) _ inv365 rows365 present365 sp365
      (fun _ => False) (fun _ _ _ _ h => h) (DefaultHeapShimMem.LoadPay pins mapping 9#5 30#5)
      (fun _ _ _ hm hp => DefaultHeapShimMem.load_pay_of_fetch hm hp) _ nodup _ _ _ _ (by decide)
      (DefaultHeapShimMem.shim_ldp real spec config rows mapping static spAligned 9#5 30#5
        (by decide) (by decide) (by decide) (by decide) catalogue _)
      (next_placed inv365.v1.pc (straight 365 (by omega) (by omega))) ob365
  have e366 : stateAt real e 366 = f := stateAt_succ_of r365
  rw [← e366] at i366 h366 wo5 pay r365 ctl365 delta365 dit365
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
  have dit367 : (stateAt real e 367).regs.PSTATE.DIT = (stateAt real e 366).regs.PSTATE.DIT :=
    (ev_succ (DefaultHeapShimEffects.shim_class real spec config rows mapping _ scope image loadBase
      base offS budget 366 catalogue (by omega) page (aligned 366) _ i366 (classE_toV tail8) rfl ob8)).1
  refine ⟨?_, dit368, dit369.trans dit368⟩
  intro j lo hi
  rcases (show j = 365 ∨ j = 366 ∨ j = 367 by omega) with rfl | rfl | rfl
  · rfl
  · exact dit365
  · exact dit367.trans dit365

#print axioms epilogue_dit_window

theorem bl_landing : Release.shimPC 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 =
    HeapV2Compose.offsetOf 0 := by decide

theorem dit_window (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)

    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (e : NativeState)
    (room : (357 + 12) ≤ budget) (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC j) (offPost : ∀ j, (357 + 8) ≤ j → j ≤ (357 + 11) → offS j = shimPC (j - (357 + 1)))

    (codeSlot : ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (inv0 : DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins)
      scope image loadBase base offS budget 0 catalogue e)
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) 112)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (E : NativeBodyDeploy.BodyEntry spec mapping base pins scope offS e)
    (codeStore : ImageTableSeparated scope base mapping (Residue.StoreBytes pins mapping))
    (slotStore : ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → ¬ Residue.StoreBytes pins mapping a)
    (low : (e.regs.gpr[30]'(by decide)).toNat < 2 ^ 55)
    (target : e.regs.gpr[30]'(by decide) = base + offS 369) :
    (∀ j, 5 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (stateAt real e 368).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧
    (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT := by
  have page := E.S.page
  have nodup := E.S.nodup
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    exact bl_landing
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.S.low
  have bodyLow : (base + offS 365).toNat < 2 ^ 55 := by
    rw [offPost 365 (by decide) (by decide)]
    exact low_of _ (by decide) E.S.low
  obtain ⟨pre, savedDit⟩ := prologue real spec config rows mapping pins scope image loadBase base offS
    budget catalogue 112 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  rw [himage, hload] at pre
  have rowRoom : DefaultHeapBudget.capacity + 2 ≤ 112 := by
    rw [DefaultHeapBudget.capacity_eq]
    decide
  have bodyRoom : 365 ≤ budget := Nat.le_trans (by decide : 365 ≤ 369) room
  obtain ⟨inv365, sp365, slot365⟩ := DefaultHeapShimBody.return_current real spec config rows mapping
    base pins scope offS budget e catalogue 112 E pre bodyRoom rowRoom bodyLow codeStore slotStore
  obtain ⟨bodyControl, _, _, rows365⟩ := DefaultHeapShimBody.body_transport real spec config rows
    mapping base pins scope offS budget e catalogue 112 E pre bodyRoom rowRoom bodyLow
  have straight : ∀ j, 365 ≤ j → j ≤ 367 → offS (j + 1) = offS j + 4#64 := by
    intro j lo hi
    rw [offPost (j + 1) (by omega) (by omega), offPost j lo (by omega),
      show j + 1 - 358 = (j - 358) + 1 by omega, shimPC_succ]
  obtain ⟨epiWindow, restore368, restore369⟩ := epilogue_dit_window real spec config rows mapping
    pins scope (HeapV2.image base) base shimStatic.separated base offS budget catalogue e
    (stateAt real e 3) room page aligned straight nodup static spAligned inv365 mrsEntry isbEntry
    bodyControl shimStatic rfl rfl offPre offPost rows365 sp365 slot365
    (by rw [pre.x30_3]; exact low) (pre.x30_3.trans target)
  have dp := DefaultHeapRun.body_deployment_of_prologue real 357 spec config rows mapping base pins
    scope offS budget (budget - 7) e catalogue 112 E rfl
    (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) rowRoom) pre
  have index (j : Nat) : stateAt real e (7 + j) = stateAt real (stateAt real e 7) j :=
    RtDit.Window.stateAt_add real e 7 j
  have bodyDit := DefaultHeapRun.body_dit real spec config rows mapping base pins (stateAt real e 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp (by omega)
  have returnDit := DefaultHeapRun.body_dit_return real spec config rows mapping base pins (stateAt real e 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp (by omega)
    (by rw [pre.x30_7]; exact bodyLow)
  rw [← index] at returnDit
  have dit365 : (stateAt real e 365).regs.PSTATE.DIT = 1#1 :=
    returnDit.trans (pre.ditOn 7 (by decide) (by decide))
  refine ⟨?_, restore368.trans savedDit, restore369.trans savedDit⟩
  intro j lo hi
  by_cases early : j ≤ 7
  · exact pre.ditOn j lo early
  by_cases body : j ≤ 364
  · have dit := bodyDit (j - 7) (by omega)
    rw [← index, show 7 + (j - 7) = j by omega] at dit
    exact dit.trans (pre.ditOn 7 (by decide) (by decide))
  · exact (epiWindow j (by omega) hi).trans dit365

#print axioms dit_window
end ReleaseProfile.DefaultHeapShimFactory
