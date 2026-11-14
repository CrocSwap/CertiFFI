-- secp CT0: DitShim243 prologue per-step EvShape (j ≤ 6), ported from the Heap shim's
-- DefaultHeapShimPrologueEvents.prologue_events onto Xlate's DitShim243.Factory.prologue (same generalizations).
import DitShim243.Pre
import DitShim243.Profiles
import DitShim243.Fetches
import DefaultHeapShimClass
import DefaultHeapShimControl
import DitShim243.Factory
import DefaultHeapShimEvents
import RtDit6.ShimPre
import RtShimG.RtDit2_Window
import RtShimG.RtDit3_ShimWindow
import RtDit4.Release
import RtShimG.ShimMemD
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
namespace SecpCt.DitPrologue
open DitShim243
open DitShim243.Pre
open NativeMteTagCheck
open DitShim243.Utils DitShim243.Geometry
open RtDit RtDit.Shim RtDit.ShimEv HeapV2StepCerts
open ArmBridge.CruxGenGuarded.Release (shimData)

theorem prologue_events (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (start : Nat) (imm26 : BitVec 26)
    (scope : Nat → Prop) (image : MemReloc.Image) 

    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (capacity : Nat) (e : NativeState)
    (room : (L + 12) ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, j < L + 12 → (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC start j) (offPost : ∀ j, (L + 8) ≤ j → j ≤ (L + 11) → offS j = shimPC start (j - (L + 1)))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (codeSlot : ImageTableSeparated scope base mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (inv0 : DefaultCurrent.CurrentInv spec config rows mapping m
      scope image base base offS budget 0 catalogue e)
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) capacity)
    (shimStatic : Fetch.CodeFacts spec mapping m scope image base start (Fetches.word imm26))
    (rowRoom : 1 ≤ capacity)
    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (slotPerm : DitShim243.SlotMem.SlotPerm m pins)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (land : offS 6 + sign_extend (imm26 ++ 0#2) 64 = offS 7)
    (low6 : (base + offS 7).toNat < 2 ^ 55) :
    (∀ j, j ≤ 7 → DefaultCurrent.CurrentInv spec config rows mapping m
      scope image base base offS budget j catalogue (stateAt real e j)) ∧
    (∀ j, j ≤ 6 → StepEvents.EvShape spec mapping (Release.shimData spec pins j)
      (stateAt real e j) (stateAt real e (j + 1))) := by
  have separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte := by
    exact shimStatic.separated
  let fetches := Fetches.of_static L spec config rows mapping m scope image base offS budget catalogue
    start imm26 shimStatic offPre offPost
  have ob0 := fetches.ob0 e inv0
  have tail1 := DitShim243.Choice.tail1 real (stateAt real e 1)
  have hw1 := DitShim243.StackClasses.hw1
  have sub1 := DitShim243.StackClasses.sub1
  have keep1all := DitShim243.StackClasses.keep1all
  have choice0 := DitShim243.Choice.bti real e
  have choice1 := DitShim243.Choice.sub_sp real (stateAt real e 1)
  have I : ∀ j, j ≤ 6 → j < budget := fun j h => by omega
  have straight : ∀ j, j ≤ 5 → offS (j + 1) = offS j + 4#64 := by
    intro j h
    rw [offPre (j + 1) (by omega), offPre j (by omega), shimPC_succ]
  have ret365 : offS (L + 8) = offS 6 + 4#64 := by
    rw [offPost (L + 8) (by omega) (by omega), offPre 6 (by omega), show L + 8 - (L + 1) = 6 + 1 by omega]; exact shimPC_succ start 6
  have N : ∀ x : NativeState, x.regs._PC + 4#64 = x.regs._PC + 4#64 := fun _ => rfl
  -- prologue chain
  obtain ⟨f, r, i1, h1, m1, _, ctl0, delta0⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image base
    separated base offS budget 0 catalogue (I 0 (by omega)) page (aligned 0 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) e inv0
    (NativeShimTails.btiC_tailVAt real e) (next_placed inv0.v1.pc (straight 0 (by omega))) ob0 choice0
  have e1 : stateAt real e 1 = f := stateAt_succ_of r
  rw [← e1] at i1 h1 m1 r ctl0 delta0
  have gcs0 := DitShim243.Profiles.class_gcs real spec config rows mapping _ scope image base
    base offS budget 0 catalogue (I 0 (by omega)) page (aligned 0 (by omega)) _ _ _ _
    (stateAt real e 0) inv0 separated (NativeShimTails.btiC_tailVAt real e) ob0 _ r
  have ob1 := fetches.ob1 _ i1
  obtain ⟨f, r1, i2, h2, m2, _, ctl1, delta1⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image base
    separated base offS budget 1 catalogue (I 1 (by omega)) page (aligned 1 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i1
    (classE_toV tail1) (next_placed i1.v1.pc (straight 1 (by omega))) ob1 choice1
  have e2 : stateAt real e 2 = f := stateAt_succ_of r1
  rw [← e2] at i2 h2 m2 r1 ctl1 delta1
  have gcs1 := DitShim243.Profiles.class_gcs real spec config rows mapping _ scope image base
    base offS budget 1 catalogue (I 1 (by omega)) page (aligned 1 (by omega)) _ _ _ _
    (stateAt real e 1) i1 separated (classE_toV tail1) ob1 _ r1
  have prof2 := DitShim243.Profiles.mrs mrsEntry
    (DitShim243.Profiles.features (ctl0.trans ctl1))
  have choice2 := DitShim243.Choice.mrs real (stateAt real e 2) prof2
  have ob2 := fetches.ob2 _ i2
  obtain ⟨f, r2, i3, h3, m3, _, ctl2, delta2⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image base
    separated base offS budget 2 catalogue (I 2 (by omega)) page (aligned 2 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i2
    (NativeShimTails.mrsDit9_tailVAt real _ prof2) (next_placed i2.v1.pc (straight 2 (by omega))) ob2 choice2
  have e3 : stateAt real e 3 = f := stateAt_succ_of r2
  rw [← e3] at i3 h3 m3 r2 ctl2 delta2
  have gcs2 := DitShim243.Profiles.class_gcs real spec config rows mapping _ scope image base
    base offS budget 2 catalogue (I 2 (by omega)) page (aligned 2 (by omega)) _ _ _ _
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
  obtain ⟨f, r3, i4, h4, wo3, k4, pay3, _, _, ev3, gcs3, dit3, ctl3, draws3, delta3, bound3⟩ :=
    DitShim243.SlotMem.shim_mem_step real spec config rows mapping _ scope image base separated
      base offS budget pins 3 catalogue (I 3 (by omega)) page (aligned 3 (by omega)) _ i3 rows3 slot3 sp3 _ codeSlot
      (DitShim243.SlotMem.StorePay pins mapping 9#5 30#5)
      (fun _ _ hg _ hp => DitShim243.SlotMem.store_pay_of_fetch hg hp)
      _ nodup _ _ _ [] (by decide)
      (DitShim243.SlotMem.shim_stp real spec config rows mapping slotPerm static spAligned 9#5 30#5
        (by decide) (by decide) (by decide) catalogue _)
      (next_placed i3.v1.pc (straight 3 (by omega))) ob3
  have e4 : stateAt real e 4 = f := stateAt_succ_of r3
  rw [← e4] at i4 h4 k4 r3 wo3 pay3 dit3 ctl3 delta3 gcs3 ev3
  have prof4 := DitShim243.Profiles.dit_on mrsEntry
    (DitShim243.Profiles.features (((ctl0.trans ctl1).trans ctl2).trans ctl3))
  have choice4 := DitShim243.Choice.dit_on real (stateAt real e 4) prof4
  have ob4 := fetches.ob4 _ i4
  obtain ⟨f, r4, i5, h5, m5, _, ctl4, delta4⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image base
    separated base offS budget 4 catalogue (I 4 (by omega)) page (aligned 4 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i4
    (NativeShimTails.ditOn_tailVAt real _ prof4) (next_placed i4.v1.pc (straight 4 (by omega))) ob4 choice4
  have e5 : stateAt real e 5 = f := stateAt_succ_of r4
  rw [← e5] at i5 h5 m5 r4 ctl4 delta4
  have gcs4 := DitShim243.Profiles.class_gcs real spec config rows mapping _ scope image base
    base offS budget 4 catalogue (I 4 (by omega)) page (aligned 4 (by omega)) _ _ _ _
    (stateAt real e 4) i4 separated (NativeShimTails.ditOn_tailVAt real _ prof4) ob4 _ r4
  have prof5 := DitShim243.Profiles.isb isbEntry
    (DitShim243.Profiles.features ((((ctl0.trans ctl1).trans ctl2).trans ctl3).trans ctl4))
  have choice5 := DitShim243.Choice.isb real (stateAt real e 5) prof5
  have ob5 := fetches.ob5 _ i5
  obtain ⟨f, r5, i6, h6, m6, _, ctl5, delta5⟩ := DefaultHeapShimClass.classStep real spec config rows mapping _ scope image base
    separated base offS budget 5 catalogue (I 5 (by omega)) page (aligned 5 (by omega)) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i5
    (NativeShimTails.isbSy_tailVAt real _ prof5) (next_placed i5.v1.pc (straight 5 (by omega))) ob5 choice5
  have e6 : stateAt real e 6 = f := stateAt_succ_of r5
  rw [← e6] at i6 h6 m6 r5 ctl5 delta5
  have gcs5 := DitShim243.Profiles.class_gcs real spec config rows mapping _ scope image base
    base offS budget 5 catalogue (I 5 (by omega)) page (aligned 5 (by omega)) _ _ _ _
    (stateAt real e 5) i5 separated (NativeShimTails.isbSy_tailVAt real _ prof5) ob5 _ r5
  have residue6 : RtBl.CallerInv.CallerResidue (stateAt real e 6) := by
    unfold RtBl.CallerInv.CallerResidue
    rw [gcs5, gcs4, gcs3, gcs2, gcs1, gcs0]
    exact residue
  have controls6 := DitShim243.Profiles.caller_controls i6 residue6
  have bl7 : blTarget imm26 (stateAt real e 6) = base + offS 7 := by
    rw [NativeEntryCallerRegisters.bl_target, i6.v1.pc, BitVec.add_assoc, land]
  have ob6 := fetches.ob6 _ i6
  obtain ⟨f, r6, i7, g7, spBL, m7, dit7, ev7, gcs7, ctl6, delta6⟩ :=
    DefaultHeapShimControl.shim_bl real spec config rows mapping _ scope image base separated
      base offS budget 6 catalogue (I 6 (by omega)) page (aligned 6 (by omega)) nodup imm26 _ i6
      (by rw [bl7]; exact low6) controls6 bl7 ob6
  have e7 : stateAt real e 7 = f := stateAt_succ_of r6
  rw [← e7] at i7 g7 m7 r6 spBL dit7 ev7 gcs7 ctl6 delta6
  have ev0 := ev_succ (DefaultHeapShimEvents.shim_ev real spec config rows mapping _ scope
    image base base offS budget 0 catalogue (by omega) page (aligned 0 (by omega)) nodup _
    (stateAt real e 0) inv0 ob0 _ tail_btiC)
  have ev1 := ev_succ (DefaultHeapShimEvents.shim_ev real spec config rows mapping _ scope
    image base base offS budget 1 catalogue (by omega) page (aligned 1 (by omega)) nodup _
    (stateAt real e 1) i1 ob1 _ (tail_classE tail1))
  have ev2 := ev_succ (DefaultHeapShimEvents.shim_ev real spec config rows mapping _ scope
    image base base offS budget 2 catalogue (by omega) page (aligned 2 (by omega)) nodup _
    (stateAt real e 2) i2 ob2 _ (tail_mrs9 prof2))
  have ev4 := ev_succ (DefaultHeapShimEvents.shim_ev real spec config rows mapping _ scope
    image base base offS budget 4 catalogue (by omega) page (aligned 4 (by omega)) nodup _
    (stateAt real e 4) i4 ob4 _ (tail_ditOn prof4))
  have ev5 := ev_succ (DefaultHeapShimEvents.shim_ev real spec config rows mapping _ scope
    image base base offS budget 5 catalogue (by omega) page (aligned 5 (by omega)) nodup _
    (stateAt real e 5) i5 ob5 _ (tail_isb prof5))
  constructor
  · intro j hi
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact inv0
    · exact i1
    · exact i2
    · exact i3
    · exact i4
    · exact i5
    · exact i6
    · exact i7
  · intro j hi
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [Release.shimData, isbData] using ev0
    · simpa [Release.shimData, isbData] using ev1
    · simpa [Release.shimData, isbData] using ev2
    · simpa [Release.shimData, isbData] using ev3
    · simpa [Release.shimData, isbData] using ev4
    · simpa [Release.shimData, isbData] using ev5
    · simpa [Release.shimData, isbData] using ev7


#print axioms prologue_events
end SecpCt.DitPrologue
