-- CT2 (Heap v1.2): run-copy of DefaultHeapShimFactory.prologue (base-v3 src-ren, sha256 in SOURCES) with the
-- conclusion strengthened from the DIT bit of x9@3 to the full x9 value at state 7. Proof body otherwise verbatim.
import RtDit6.ShimPre
import DefaultHeapShimClass
import DefaultHeapShimPre
import DefaultHeapShimProfiles
import DefaultHeapShimFetch
import DefaultHeapShimMem
import DefaultHeapShimEffects
import DefaultHeapShimControl
import RtShimG.RtDit2_Window
import RtShimG.RtDit3_ShimWindow
import RtDit4.Release
import RtShimG.ShimMemD
import HeapV2StepCerts.Residue.RAssembly
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
namespace CT2Heap
/-- The MRS DIT image of a DIT bit (x9 after `MRS x9, DIT`). -/
def ditImage (b : BitVec 1) : BitVec 64 := ((0#39).append b).append 0#24
theorem enc_bit (b : BitVec 1) : (((0#39 : BitVec 39).append b).append (0#24 : BitVec 24)).extractLsb 24 24 = b := by
  revert b; decide
end CT2Heap

namespace ReleaseProfile.CT2HeapX9
open DefaultHeapShimPre
open NativeMteTagCheck
open RtDit.Release
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts
open ArmBridge.CruxGenGuarded.Release (shimPC shimData shimMap ShimPrologue ShimEpilogue)

set_option maxHeartbeats 400000 in
theorem prologueX9 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)

    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (capacity : Nat) (e : NativeState)
    (room : (357 + 12) ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC j) (offPost : ∀ j, (357 + 8) ≤ j → j ≤ (357 + 11) → offS j = shimPC (j - (357 + 1)))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (codeSlot : ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (inv0 : DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins)
      scope image loadBase base offS budget 0 catalogue e)
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) capacity)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)
    (rowRoom : 1 ≤ capacity)
    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7)
    (low6 : (base + offS 7).toNat < 2 ^ 55) :
    ShimPreMG real 357 spec config rows mapping pins scope image loadBase base offS budget catalogue capacity e ∧
    (stateAt real e 3).regs.gpr[9] = CT2Heap.ditImage e.regs.PSTATE.DIT ∧
    (stateAt real e 7).regs.gpr[9] = CT2Heap.ditImage e.regs.PSTATE.DIT := by
  have separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte := by
    simpa only [hload] using shimStatic.separated
  let fetches := DefaultHeapShimFetch.of_static real spec config rows mapping pins scope image loadBase
    base offS budget catalogue shimStatic himage hload offPre offPost
  have ob0 := fetches.ob0 e inv0
  have tail1 := DefaultHeapShimChoice.tail1 real (stateAt real e 1)
  have hw1 := NativeShimTails.hw1
  have sub1 := NativeShimTails.sub1
  have keep1all := NativeShimTails.keep1all
  have choice0 := DefaultHeapShimChoice.bti real e
  have choice1 := DefaultHeapShimChoice.sub_sp real (stateAt real e 1)
  have I : ∀ j, j ≤ 6 → j < budget := fun j h => by omega
  have straight : ∀ j, j ≤ 5 → offS (j + 1) = offS j + 4#64 := by
    intro j h
    rw [offPre (j + 1) (by omega), offPre j (by omega), shimPC_succ]
  have ret365 : offS (357 + 8) = offS 6 + 4#64 := by
    rw [offPost (357 + 8) (by omega) (by omega), offPre 6 (by omega), show 357 + 8 - (357 + 1) = 6 + 1 by omega]; exact shimPC_succ 6
  have N : ∀ x : NativeState, x.regs._PC + 4#64 = x.regs._PC + 4#64 := fun _ => rfl
  -- prologue chain
  obtain ⟨f, r, i1, h1, m1, _, ctl0, delta0⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 0 catalogue (I 0 (by omega)) page (aligned 0) _ _ _ _ (fun x => x.regs._PC + 4#64) e inv0
    (NativeShimTails.btiC_tailVAt real e) (next_placed inv0.v1.pc (straight 0 (by omega))) ob0 choice0
  have e1 : stateAt real e 1 = f := stateAt_succ_of r
  rw [← e1] at i1 h1 m1 r ctl0 delta0
  have gcs0 := DefaultHeapShimProfiles.class_gcs real spec config rows mapping _ scope image loadBase
    base offS budget 0 catalogue (I 0 (by omega)) page (aligned 0) _ _ _ _
    (stateAt real e 0) inv0 separated (NativeShimTails.btiC_tailVAt real e) ob0 _ r
  have ob1 := fetches.ob1 _ i1
  obtain ⟨f, r1, i2, h2, m2, _, ctl1, delta1⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 1 catalogue (I 1 (by omega)) page (aligned 1) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i1
    (classE_toV tail1) (next_placed i1.v1.pc (straight 1 (by omega))) ob1 choice1
  have e2 : stateAt real e 2 = f := stateAt_succ_of r1
  rw [← e2] at i2 h2 m2 r1 ctl1 delta1
  have gcs1 := DefaultHeapShimProfiles.class_gcs real spec config rows mapping _ scope image loadBase
    base offS budget 1 catalogue (I 1 (by omega)) page (aligned 1) _ _ _ _
    (stateAt real e 1) i1 separated (classE_toV tail1) ob1 _ r1
  have prof2 := DefaultHeapShimProfiles.mrs mrsEntry
    (DefaultHeapShimProfiles.features (ctl0.trans ctl1))
  have choice2 := DefaultHeapShimChoice.mrs real (stateAt real e 2) prof2
  have ob2 := fetches.ob2 _ i2
  obtain ⟨f, r2, i3, h3, m3, _, ctl2, delta2⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 2 catalogue (I 2 (by omega)) page (aligned 2) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i2
    (NativeShimTails.mrsDit9_tailVAt real _ prof2) (next_placed i2.v1.pc (straight 2 (by omega))) ob2 choice2
  have e3 : stateAt real e 3 = f := stateAt_succ_of r2
  rw [← e3] at i3 h3 m3 r2 ctl2 delta2
  have gcs2 := DefaultHeapShimProfiles.class_gcs real spec config rows mapping _ scope image loadBase
    base offS budget 2 catalogue (I 2 (by omega)) page (aligned 2) _ _ _ _
    (stateAt real e 2) i2 separated (NativeShimTails.mrsDit9_tailVAt real _ prof2) ob2 _ r2
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
  have ob3 := fetches.ob3 _ i3
  obtain ⟨f, r3, i4, h4, wo3, k4, pay3, _, _, _, gcs3, dit3, ctl3, draws3, delta3, bound3⟩ :=
    DefaultHeapShimMem.shim_mem_step real spec config rows mapping _ scope image loadBase separated
      base offS budget pins 3 catalogue (I 3 (by omega)) page (aligned 3) _ i3 rows3 slot3 sp3 _ codeSlot
      (DefaultHeapShimMem.StorePay pins mapping 9#5 30#5)
      (fun _ _ hg _ hp => DefaultHeapShimMem.store_pay_of_fetch hg hp)
      _ nodup _ _ _ [] (by decide)
      (DefaultHeapShimMem.shim_stp real spec config rows mapping static spAligned 9#5 30#5
        (by decide) (by decide) (by decide) catalogue _)
      (next_placed i3.v1.pc (straight 3 (by omega))) ob3
  have e4 : stateAt real e 4 = f := stateAt_succ_of r3
  rw [← e4] at i4 h4 k4 r3 wo3 pay3 dit3 ctl3 delta3 gcs3
  have prof4 := DefaultHeapShimProfiles.dit_on mrsEntry
    (DefaultHeapShimProfiles.features (((ctl0.trans ctl1).trans ctl2).trans ctl3))
  have choice4 := DefaultHeapShimChoice.dit_on real (stateAt real e 4) prof4
  have ob4 := fetches.ob4 _ i4
  obtain ⟨f, r4, i5, h5, m5, _, ctl4, delta4⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 4 catalogue (I 4 (by omega)) page (aligned 4) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i4
    (NativeShimTails.ditOn_tailVAt real _ prof4) (next_placed i4.v1.pc (straight 4 (by omega))) ob4 choice4
  have e5 : stateAt real e 5 = f := stateAt_succ_of r4
  rw [← e5] at i5 h5 m5 r4 ctl4 delta4
  have gcs4 := DefaultHeapShimProfiles.class_gcs real spec config rows mapping _ scope image loadBase
    base offS budget 4 catalogue (I 4 (by omega)) page (aligned 4) _ _ _ _
    (stateAt real e 4) i4 separated (NativeShimTails.ditOn_tailVAt real _ prof4) ob4 _ r4
  have prof5 := DefaultHeapShimProfiles.isb isbEntry
    (DefaultHeapShimProfiles.features ((((ctl0.trans ctl1).trans ctl2).trans ctl3).trans ctl4))
  have choice5 := DefaultHeapShimChoice.isb real (stateAt real e 5) prof5
  have ob5 := fetches.ob5 _ i5
  obtain ⟨f, r5, i6, h6, m6, _, ctl5, delta5⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image loadBase
    separated base offS budget 5 catalogue (I 5 (by omega)) page (aligned 5) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i5
    (NativeShimTails.isbSy_tailVAt real _ prof5) (next_placed i5.v1.pc (straight 5 (by omega))) ob5 choice5
  have e6 : stateAt real e 6 = f := stateAt_succ_of r5
  rw [← e6] at i6 h6 m6 r5 ctl5 delta5
  have gcs5 := DefaultHeapShimProfiles.class_gcs real spec config rows mapping _ scope image loadBase
    base offS budget 5 catalogue (I 5 (by omega)) page (aligned 5) _ _ _ _
    (stateAt real e 5) i5 separated (NativeShimTails.isbSy_tailVAt real _ prof5) ob5 _ r5
  have residue6 : RtBl.CallerInv.CallerResidue (stateAt real e 6) := by
    unfold RtBl.CallerInv.CallerResidue
    rw [gcs5, gcs4, gcs3, gcs2, gcs1, gcs0]
    exact residue
  have controls6 := DefaultHeapShimProfiles.caller_controls i6 residue6
  have bl7 : blTarget NativeShimFetch.imm26 (stateAt real e 6) = base + offS 7 := by
    rw [NativeEntryCallerRegisters.bl_target, i6.v1.pc, BitVec.add_assoc, land]
  have ob6 := fetches.ob6 _ i6
  obtain ⟨f, r6, i7, g7, spBL, m7, dit7, ev7, gcs7, ctl6, delta6⟩ :=
    DefaultHeapShimControl.shim_bl real spec config rows mapping _ scope image loadBase separated
      base offS budget 6 catalogue (I 6 (by omega)) page (aligned 6) nodup NativeShimFetch.imm26 _ i6
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
  have link : (stateAt real e 7).regs.gpr[30] = base + offS (357 + 8) := by
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
    loadBase base offS budget 4 catalogue (I 4 (by omega)) page (aligned 4) _ i4 prof4 ob4)).1
  have d6 : (stateAt real e 6).regs.PSTATE.DIT = (stateAt real e 5).regs.PSTATE.DIT := (ev_succ (DefaultHeapShimEffects.shim_class real spec
    config rows mapping _ scope image loadBase base offS budget 5 catalogue (I 5 (by omega)) page (aligned 5) _ i5
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
  have savedDit := DefaultHeapShimProfiles.saved_dit real spec config rows mapping _ scope image loadBase
    base offS budget catalogue e inv0 i1 i2 (by omega) page aligned ob0 (classE_toV tail1) hw1 ob1 prof2 ob2
  -- CT2: full x9 value at 7 (MRS DIT at step 2; savedDit pins DIT@2; steps 3..6 keep x9; BL writes x30 only)
  obtain ⟨fin9, run9, saved9, _, _⟩ := DefaultHeapShimEffects.shim_mrs9 real spec config rows mapping _ scope image loadBase
    base offS budget 2 catalogue (I 2 (by omega)) page (aligned 2) _ i2 prof2 ob2
  have e9 : stateAt real e 3 = fin9 := stateAt_succ_of run9
  rw [← e9] at saved9
  have d2 : (stateAt real e 2).regs.PSTATE.DIT = e.regs.PSTATE.DIT := by
    have h := savedDit; rw [saved9] at h; rw [← h]; exact (CT2Heap.enc_bit _).symm
  have x9_3 : (stateAt real e 3).regs.gpr[9] = CT2Heap.ditImage e.regs.PSTATE.DIT := by
    rw [saved9, d2]; rfl
  have k6 := RtSaved.kept_reg h6 (9 : Fin 31) rfl
  have k5 := RtSaved.kept_reg h5 (9 : Fin 31) rfl
  have k4 := RtSaved.kept_reg h4 (9 : Fin 31) rfl
  have x9_7 : (stateAt real e 7).regs.gpr[9] = CT2Heap.ditImage e.regs.PSTATE.DIT := by
    rw [g7, Vector.getElem_set_ne _ _ (by decide)]
    exact k6.trans (k5.trans (k4.trans x9_3))
  refine ⟨?_, x9_3, x9_7⟩
  refine { toShimPreG := ?_, memPre := memPre }
  refine
    { statusRows := entryRows, control7 := allControl, choice7 := ⟨draws3, allChoice, bound3⟩, runs := fun j hj => ?_, inv := fun j hj => ?_, inv7 := i7, sp3 := sp3, sp7 := sp7, slot4 := slot4,
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


#print axioms prologueX9
end ReleaseProfile.CT2HeapX9
