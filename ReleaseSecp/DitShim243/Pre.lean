import DitShim243.Geometry
import DitShim243.SlotMem
import DitShim243.Utils
import DefaultHeapShimClass
import DefaultHeapShimControl
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
open NativeEntryCallerParts ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
open ReleaseProfile
namespace DitShim243.Pre
open NativeMteTagCheck
open DitShim243.Utils DitShim243.Geometry
open RtDit RtDit.Shim RtDit.ShimEv HeapV2StepCerts

/-- The shim prologue s0..s6 along the actual run (body-independent): shared by ShimPrologue, ShimPrologueT,
the body/epilogue chain and ShimKeepG. -/
structure ShimPreG (real : Type) [Sail.SailReal real] (L : Nat) {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (start : Nat)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (capacity : Nat) (e : NativeState) : Prop where
  runs : ∀ j, j ≤ 6 → modelStep real (stateAt real e j) = .ok () (stateAt real e (j + 1))
  inv : ∀ j, j ≤ 6 → DefaultCurrent.CurrentInv spec config rows mapping m
    scope image loadBase base offS budget j catalogue (stateAt real e j)
  inv7 : DefaultCurrent.CurrentInv spec config rows mapping m
    scope image loadBase base offS budget 7 catalogue (stateAt real e 7)
  statusRows : TagStatusRows e (e.choiceOcc.getD 1354 0) capacity
  control7 : RtPremC.CtlRel spec e (stateAt real e 7)
  controlPrefix : ∀ j, j ≤ 7 → RtPremC.CtlRel spec e (stateAt real e j)
  choice7 : ∃ draws, ChoiceDelta e (stateAt real e 7) draws ∧ draws ≤ 1
  slot3 : RtShim.SlotPrem.ShimSlotPresent pins mapping (stateAt real e 3)
  caller6 : CallerControls (stateAt real e 6)
  choicePrefix : ∀ j, j ≤ 7 → ∃ draws, NativeMteTagCheck.ChoiceDelta e (stateAt real e j) draws ∧ draws ≤ 1
  sp3 : (stateAt real e 3).regs.SP_EL0 = BitVec.ofNat 64 pins.sp
  sp7 : (stateAt real e 7).regs.SP_EL0 = BitVec.ofNat 64 pins.sp
  slot4 : SlotHas pins mapping (ArmCertMem.StpEval.stpData (stateAt real e 3) 9#5 30#5) (stateAt real e 4)
  mem47 : ∀ a : Nat, (stateAt real e 7).mem[a]? = (stateAt real e 4).mem[a]?
  x30_3 : (stateAt real e 3).regs.gpr[30] = e.regs.gpr[30]
  x30_7 : (stateAt real e 7).regs.gpr[30] = base + offS (L + 8)
  keepPre : ∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 → (stateAt real e 7).regs.gpr[i.val] = e.regs.gpr[i.val]
  residue7 : RtBl.CallerInv.CallerResidue (stateAt real e 7)
  ditOn : ∀ j, 5 ≤ j → j ≤ 7 → (stateAt real e j).regs.PSTATE.DIT = 1#1

/-- ShimPreG + Memory's prologue memory frame (ShimFrameV memPre): state 7 equals the entry off the 16-byte slot. -/
structure ShimPreMG (real : Type) [Sail.SailReal real] (L : Nat) {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (start : Nat)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (capacity : Nat) (e : NativeState)
    extends ShimPreG real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e : Prop where
  memPre : ∀ a, ¬ RtShim2.ShimMem.slotBytes pins mapping a → (stateAt real e 7).mem[a]? = e.mem[a]?

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Release.shim_preG"
  (← IO.getStderr).flush

theorem shim_preG (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (start : Nat)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (capacity : Nat) (e : NativeState) (callerPC : BitVec 64)
    (room : (L + 12) ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, j < L + 12 → (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC start j) (offPost : ∀ j, (L + 8) ≤ j → j ≤ (L + 11) → offS j = shimPC start (j - (L + 1)))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (codeSlot : ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (inv0 : DefaultCurrent.CurrentInv spec config rows mapping m
      scope image loadBase base offS budget 0 catalogue e)
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) capacity)
    (rowRoom : 1 ≤ capacity)
    (choice0 : DefaultScalarTrace.TailChoiceAt real e NativeEntryDispatch.BtiC.word)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (slotPerm : DitShim243.SlotMem.SlotPerm m pins)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)
    (ob0 : FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word (stateAt real e 0))
    {w1 : BitVec 32} {writes1 : NativeEntry.Effects.Writes} {K1 : Int} {us1 : List (RegBind.Reg × RegBind.Upd)}
    (tail1 : RegValE.ClassTailVAt real w1 writes1 K1 (stateAt real e 1) ((stateAt real e 1).regs._PC + 4#64) us1)
    (choice1 : DefaultScalarTrace.TailChoiceAt real (stateAt real e 1) w1)
    (choice2 : DefaultScalarTrace.TailChoiceAt real (stateAt real e 2) (NativeEntryDispatch.MrsDit.word 9#5))
    (choice4 : DefaultScalarTrace.TailChoiceAt real (stateAt real e 4) NativeEntryDispatch.DitOn.word)
    (choice5 : DefaultScalarTrace.TailChoiceAt real (stateAt real e 5) NativeEntryDispatch.IsbSy.word)
    (hw1 : writes1.dit = false) (sub1 : RegBind.updOf us1 .sp = .set .sp (-16))
    (keep1all : ∀ i : Fin 31, RegBind.updOf us1 (.x i) = .keep)
    (ob1 : FetchObligations spec config rows mapping w1 (stateAt real e 1))
    (prof2 : NativeEntryAdapters.MrsDit.Profile (stateAt real e 2))
    (ob2 : FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) (stateAt real e 2))
    (ob3 : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7)
      (stateAt real e 3))
    (prof4 : NativeEntryAdapters.DitOn.Profile (stateAt real e 4))
    (ob4 : FetchObligations spec config rows mapping NativeEntryDispatch.DitOn.word (stateAt real e 4))
    (prof5 : NativeEntryAdapters.IsbSy.Profile (stateAt real e 5))
    (ob5 : FetchObligations spec config rows mapping NativeEntryDispatch.IsbSy.word (stateAt real e 5))
    (imm26 : BitVec 26) (controls6 : CallerControls (stateAt real e 6))
    (bl7 : blTarget imm26 (stateAt real e 6) = base + offS 7)
    (low6 : (base + offS 7).toNat < 2 ^ 55)
    (ob6 : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) (stateAt real e 6)) :
    ShimPreMG real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e := by
  have I : ∀ j, j ≤ 6 → j < budget := fun j h => by omega
  have straight : ∀ j, j ≤ 5 → offS (j + 1) = offS j + 4#64 := by
    intro j h
    rw [offPre (j + 1) (by omega), offPre j (by omega), shimPC_succ]
  have ret365 : offS (L + 8) = offS 6 + 4#64 := by
    rw [offPost (L + 8) (by omega) (by omega), offPre 6 (by omega), show L + 8 - (L + 1) = 6 + 1 by omega]; exact shimPC_succ start 6
  have N : ∀ x : NativeState, x.regs._PC + 4#64 = x.regs._PC + 4#64 := fun _ => rfl
  -- prologue chain
  obtain ⟨f, r, i1, h1, m1, _, ctl0, delta0⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 0 catalogue (I 0 (by omega)) page (aligned 0 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) e inv0
    (NativeShimTails.btiC_tailVAt real e) (next_placed inv0.v1.pc (straight 0 (by omega))) ob0 choice0
  have e1 : stateAt real e 1 = f := stateAt_succ_of r
  rw [← e1] at i1 h1 m1 r ctl0 delta0
  obtain ⟨f, r1, i2, h2, m2, _, ctl1, delta1⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 1 catalogue (I 1 (by omega)) page (aligned 1 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i1
    (classE_toV tail1) (next_placed i1.v1.pc (straight 1 (by omega))) ob1 choice1
  have e2 : stateAt real e 2 = f := stateAt_succ_of r1
  rw [← e2] at i2 h2 m2 r1 ctl1 delta1
  obtain ⟨f, r2, i3, h3, m3, _, ctl2, delta2⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 2 catalogue (I 2 (by omega)) page (aligned 2 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i2
    (NativeShimTails.mrsDit9_tailVAt real _ prof2) (next_placed i2.v1.pc (straight 2 (by omega))) ob2 choice2
  have e3 : stateAt real e 3 = f := stateAt_succ_of r2
  rw [← e3] at i3 h3 m3 r2 ctl2 delta2
  have k9 : ∀ i : Fin 31, i.val ≠ 9 → RegBind.updOf [(RegBind.Reg.x 9, RegBind.Upd.drop)] (.x i) = .keep := by
    intro i hi
    simp only [RegBind.updOf, List.find?]
    have : (RegBind.Reg.x 9 = RegBind.Reg.x i) = False := by
      simp only [RegBind.Reg.x.injEq, eq_iff_iff, iff_false]; intro h; exact hi (by rw [← h]; rfl)
    simp [this]
  have sp1 : (stateAt real e 1).regs.SP_EL0 = e.regs.SP_EL0 := h1 .sp
  have sp2 : (stateAt real e 2).regs.SP_EL0 = (stateAt real e 1).regs.SP_EL0 + BitVec.ofInt 64 (-16) := by
    have h := h2 .sp; rw [sub1] at h; exact h
  have z16 : BitVec.ofInt 64 16 + BitVec.ofInt 64 (-16) = 0#64 := by decide
  have sp3 : (stateAt real e 3).regs.SP_EL0 = BitVec.ofNat 64 pins.sp := by
    have h : (stateAt real e 3).regs.SP_EL0 = (stateAt real e 2).regs.SP_EL0 := h3 .sp
    rw [h, sp2, sp1, spE, BitVec.add_assoc, z16, BitVec.add_zero]
  have slot3 : RtShim.SlotPrem.ShimSlotPresent pins mapping (stateAt real e 3) := fun n hn i hi => by
    rw [m3, m2, m1]; exact slotE n hn i hi
  have prefix3 : ChoiceDelta e (stateAt real e 3) 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans (choice_delta_trans delta0 delta1) delta2
  have rows3 : TagStatusRows (stateAt real e 3) ((stateAt real e 3).choiceOcc.getD 1354 0) 1 := by
    intro index within
    unfold TagStatusRows at *
    rw [prefix3.1, prefix3.2, Nat.add_zero]
    exact entryRows index (by omega)
  obtain ⟨f, r3, i4, h4, wo3, k4, pay3, _, _, _, _, dit3, ctl3, draws3, delta3, bound3⟩ :=
    DitShim243.SlotMem.shim_mem_step real spec config rows mapping _ scope image loadBase separated
      base offS budget pins 3 catalogue (I 3 (by omega)) page (aligned 3 (by omega)) _ i3 rows3 slot3 sp3 _ codeSlot
      (DitShim243.SlotMem.StorePay pins mapping 9#5 30#5)
      (fun _ _ hg _ hp => DitShim243.SlotMem.store_pay_of_fetch hg hp)
      _ nodup _ _ _ [] (by decide)
      (DitShim243.SlotMem.shim_stp real spec config rows mapping slotPerm static spAligned 9#5 30#5
        (by decide) (by decide) (by decide) catalogue _)
      (next_placed i3.v1.pc (straight 3 (by omega))) ob3
  have e4 : stateAt real e 4 = f := stateAt_succ_of r3
  rw [← e4] at i4 h4 k4 r3 wo3 pay3 dit3 ctl3 delta3
  obtain ⟨f, r4, i5, h5, m5, _, ctl4, delta4⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 4 catalogue (I 4 (by omega)) page (aligned 4 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i4
    (NativeShimTails.ditOn_tailVAt real _ prof4) (next_placed i4.v1.pc (straight 4 (by omega))) ob4 choice4
  have e5 : stateAt real e 5 = f := stateAt_succ_of r4
  rw [← e5] at i5 h5 m5 r4 ctl4 delta4
  obtain ⟨f, r5, i6, h6, m6, _, ctl5, delta5⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 5 catalogue (I 5 (by omega)) page (aligned 5 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i5
    (NativeShimTails.isbSy_tailVAt real _ prof5) (next_placed i5.v1.pc (straight 5 (by omega))) ob5 choice5
  have e6 : stateAt real e 6 = f := stateAt_succ_of r5
  rw [← e6] at i6 h6 m6 r5 ctl5 delta5
  obtain ⟨f, r6, i7, g7, spBL, m7, dit7, ev7, gcs7, ctl6, delta6⟩ :=
    DefaultHeapShimControl.shim_bl real spec config rows mapping _ scope image loadBase separated
      base offS budget 6 catalogue (I 6 (by omega)) page (aligned 6 (by omega)) nodup imm26 _ i6
      (by rw [bl7]; exact low6) controls6 bl7 ob6
  have e7 : stateAt real e 7 = f := stateAt_succ_of r6
  rw [← e7] at i7 g7 m7 r6 spBL dit7 ev7 gcs7 ctl6 delta6
  -- X2/X3/X30 through the prologue
  have keepPre : ∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 →
      (stateAt real e 7).regs.gpr[i.val] = e.regs.gpr[i.val] := by
    intro i n9 n30
    rw [g7, Vector.getElem_set_ne _ _ (by omega), RtSaved.kept_reg h6 i rfl, RtSaved.kept_reg h5 i rfl,
      RtSaved.kept_reg h4 i rfl, RtSaved.kept_reg h3 i (k9 i n9), RtSaved.kept_reg h2 i (keep1all i),
      RtSaved.kept_reg h1 i rfl]
  have x30_3 : (stateAt real e 3).regs.gpr[30] = e.regs.gpr[30] := by
    rw [RtSaved.kept_reg h3 ⟨30, by decide⟩ (k9 _ (by decide)), RtSaved.kept_reg h2 ⟨30, by decide⟩ (keep1all _),
      RtSaved.kept_reg h1 ⟨30, by decide⟩ rfl]
  have link : (stateAt real e 7).regs.gpr[30] = base + offS (L + 8) := by
    rw [g7, Vector.getElem_set_self, i6.v1.pc, ret365, BitVec.add_assoc]
  have sp7 : (stateAt real e 7).regs.SP_EL0 = BitVec.ofNat 64 pins.sp := by
    have k5 : (stateAt real e 5).regs.SP_EL0 = (stateAt real e 4).regs.SP_EL0 := h5 .sp
    have k6 : (stateAt real e 6).regs.SP_EL0 = (stateAt real e 5).regs.SP_EL0 := h6 .sp
    have k4 : (stateAt real e 4).regs.SP_EL0 = (stateAt real e 3).regs.SP_EL0 := h4 .sp
    rw [spBL, k6, k5, k4, sp3]
  have slot4 : SlotHas pins mapping (ArmCertMem.StpEval.stpData (stateAt real e 3) 9#5 30#5)
      (stateAt real e 4) := by
    intro n hn i hi
    exact pay3 n hn i hi
  have d5 : (stateAt real e 5).regs.PSTATE.DIT = 1#1 := (ev_succ (DefaultHeapShimEffects.shim_ditOn real spec config rows mapping _ scope image
    loadBase base offS budget 4 catalogue (I 4 (by omega)) page (aligned 4 (by omega)) _ i4 prof4 ob4)).1
  have d6 : (stateAt real e 6).regs.PSTATE.DIT = (stateAt real e 5).regs.PSTATE.DIT := (ev_succ (DefaultHeapShimEffects.shim_class real spec
    config rows mapping _ scope image loadBase base offS budget 5 catalogue (I 5 (by omega)) page (aligned 5 (by omega)) _ i5
    (NativeShimTails.isbSy_tailVAt real _ prof5) rfl ob5)).1
  have d7 : (stateAt real e 7).regs.PSTATE.DIT = (stateAt real e 6).regs.PSTATE.DIT := dit7
  have residue7 : RtBl.CallerInv.CallerResidue (stateAt real e 7) := by
    unfold RtBl.CallerInv.CallerResidue
    rw [gcs7]
    exact controls6.gcsEn
  have memPre : ∀ a, ¬ RtShim2.ShimMem.slotBytes pins mapping a → (stateAt real e 7).mem[a]? = e.mem[a]? := by
    intro a ha
    have w3 := wo3 a ha
    rw [m7, m6, m5, w3, m3, m2, m1]
  have allChoice : ChoiceDelta e (stateAt real e 7) draws3 := by
    simpa only [Nat.zero_add, Nat.add_zero] using
      choice_delta_trans (choice_delta_trans (choice_delta_trans
        (choice_delta_trans prefix3 delta3) delta4) delta5) delta6
  have allControl : RtPremC.CtlRel spec e (stateAt real e 7) :=
    (((((ctl0.trans ctl1).trans ctl2).trans ctl3).trans ctl4).trans ctl5).trans ctl6
  have prefixControl : ∀ j, j ≤ 7 → RtPremC.CtlRel spec e (stateAt real e j) := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact RtPremC.CtlRel.refl spec e
    · exact ctl0
    · exact (ctl0).trans ctl1
    · exact ((ctl0).trans ctl1).trans ctl2
    · exact (((ctl0).trans ctl1).trans ctl2).trans ctl3
    · exact ((((ctl0).trans ctl1).trans ctl2).trans ctl3).trans ctl4
    · exact (((((ctl0).trans ctl1).trans ctl2).trans ctl3).trans ctl4).trans ctl5
    · exact ((((((ctl0).trans ctl1).trans ctl2).trans ctl3).trans ctl4).trans ctl5).trans ctl6
  have prefixChoices : ∀ j, j ≤ 7 → ∃ draws, NativeMteTagCheck.ChoiceDelta e (stateAt real e j) draws ∧ draws ≤ 1 := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0,NativeMteTagCheck.choice_delta_refl e,by omega⟩
    · exact ⟨0,delta0,by omega⟩
    · exact ⟨0,by simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans delta0 delta1,by omega⟩
    · exact ⟨0,prefix3,by omega⟩
    · exact ⟨draws3,by simpa only [Nat.zero_add] using NativeMteTagCheck.choice_delta_trans prefix3 delta3,bound3⟩
    · exact ⟨draws3,by simpa only [Nat.zero_add,Nat.add_zero] using
        NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans prefix3 delta3) delta4,bound3⟩
    · exact ⟨draws3,by simpa only [Nat.zero_add,Nat.add_zero] using
        NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans prefix3 delta3) delta4) delta5,bound3⟩
    · exact ⟨draws3,allChoice,bound3⟩
  refine { toShimPreG := ?_, memPre := memPre }
  refine
    { statusRows := entryRows, control7 := allControl, controlPrefix := prefixControl, choice7 := ⟨draws3, allChoice, bound3⟩, runs := fun j hj => ?_, inv := fun j hj => ?_, inv7 := i7, sp3 := sp3, slot3 := slot3, caller6 := controls6, choicePrefix := prefixChoices, sp7 := sp7, slot4 := slot4,
      mem47 := fun a => by rw [m7, m6, m5], x30_3 := x30_3, x30_7 := link, keepPre := keepPre, residue7 := residue7,
      ditOn := fun j lo hi => ?_ }
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact inv0
    · exact i1
    · exact i2
    · exact i3
    · exact i4
    · exact i5
    · exact i6
  · rcases (show j = 5 ∨ j = 6 ∨ j = 7 by omega) with rfl | rfl | rfl
    · exact d5
    · exact d6.trans d5
    · exact d7.trans (d6.trans d5)

#print axioms shim_preG
end DitShim243.Pre
