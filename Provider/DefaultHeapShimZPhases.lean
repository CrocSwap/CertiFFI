import RtDit6.ShimPre
import DefaultHeapShimClass
import DefaultHeapShimZ
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
namespace ReleaseProfile.DefaultHeapShimFactory
open DefaultHeapShimPre
open NativeMteTagCheck
open RtDit.Release
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts
open ArmBridge.CruxGenGuarded.Release (shimPC shimData shimMap ShimPrologue ShimEpilogue)


theorem prologue_z (real : Type) [Sail.SailReal real]
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
    (stateAt real e 7).regs._Z = e.regs._Z := by
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
  obtain ⟨f, r3, i4, h4, wo3, k4, pay3, z3, _, _, gcs3, dit3, ctl3, draws3, delta3, bound3⟩ :=
    DefaultHeapShimMem.shim_mem_step real spec config rows mapping _ scope image loadBase separated
      base offS budget pins 3 catalogue (I 3 (by omega)) page (aligned 3) _ i3 rows3 slot3 sp3 _ codeSlot
      (DefaultHeapShimMem.StorePay pins mapping 9#5 30#5)
      (fun _ _ hg _ hp => DefaultHeapShimMem.store_pay_of_fetch hg hp)
      _ nodup _ _ _ [] (by decide)
      (DefaultHeapShimMem.shim_stp real spec config rows mapping static spAligned 9#5 30#5
        (by decide) (by decide) (by decide) catalogue _)
      (next_placed i3.v1.pc (straight 3 (by omega))) ob3
  have e4 : stateAt real e 4 = f := stateAt_succ_of r3
  rw [← e4] at i4 h4 k4 r3 wo3 pay3 dit3 ctl3 delta3 gcs3 z3
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
  have z0 := ev_succ (DefaultHeapShimZ.shim_z real spec config rows mapping _ scope image loadBase
    base offS budget 0 catalogue (by omega) page (aligned 0) _ (stateAt real e 0) inv0 ob0 (RtDit.Release.z_class (NativeShimTails.btiC_tailVAt real e) rfl))
  have z1 := ev_succ (DefaultHeapShimZ.shim_z real spec config rows mapping _ scope image loadBase
    base offS budget 1 catalogue (by omega) page (aligned 1) _ (stateAt real e 1) i1 ob1 (RtDit.Release.z_classE tail1))
  have z2 := ev_succ (DefaultHeapShimZ.shim_z real spec config rows mapping _ scope image loadBase
    base offS budget 2 catalogue (by omega) page (aligned 2) _ (stateAt real e 2) i2 ob2 (RtDit.Release.z_class (NativeShimTails.mrsDit9_tailVAt real _ prof2) rfl))
  have z4 := ev_succ (DefaultHeapShimZ.shim_z real spec config rows mapping _ scope image loadBase
    base offS budget 4 catalogue (by omega) page (aligned 4) _ (stateAt real e 4) i4 ob4 (RtDit.Release.z_class (NativeShimTails.ditOn_tailVAt real _ prof4) rfl))
  have z5 := ev_succ (DefaultHeapShimZ.shim_z real spec config rows mapping _ scope image loadBase
    base offS budget 5 catalogue (by omega) page (aligned 5) _ (stateAt real e 5) i5 ob5 (RtDit.Release.z_class (NativeShimTails.isbSy_tailVAt real _ prof5) rfl))
  have z6 := ev_succ (DefaultHeapShimZ.shim_bl_z real spec config rows mapping _ scope image loadBase
    separated base offS budget 6 catalogue (by omega) page (aligned 6) nodup NativeShimFetch.imm26
    (stateAt real e 6) i6 (by rw [bl7]; exact low6) controls6 bl7 ob6)
  exact z6.trans (z5.trans (z4.trans (z3.trans (z2.trans (z1.trans z0)))))

#print axioms prologue_z

theorem epilogue_z (real : Type) [Sail.SailReal real]
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
    (stateAt real e 369).regs._Z = (stateAt real e 365).regs._Z := by
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
  obtain ⟨f, r365, i366, h366, wo5, _, pay, z365, _, _, _, _, ctl365, draws365, delta365, bound365⟩ :=
    DefaultHeapShimMem.shim_mem_step real spec config rows mapping (shimMap spec mapping base pins) scope image loadBase separated
      base offS budget pins 365 catalogue (by omega) page (aligned 365) _ inv365 rows365 present365 sp365
      (fun _ => False) (fun _ _ _ _ h => h) (DefaultHeapShimMem.LoadPay pins mapping 9#5 30#5)
      (fun _ _ _ hm hp => DefaultHeapShimMem.load_pay_of_fetch hm hp) _ nodup _ _ _ _ (by decide)
      (DefaultHeapShimMem.shim_ldp real spec config rows mapping static spAligned 9#5 30#5
        (by decide) (by decide) (by decide) (by decide) catalogue _)
      (next_placed inv365.v1.pc (straight 365 (by omega) (by omega))) ob365
  have e366 : stateAt real e 366 = f := stateAt_succ_of r365
  rw [← e366] at i366 h366 wo5 pay r365 ctl365 delta365 z365
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
  have z366 := ev_succ (DefaultHeapShimZ.shim_z real spec config rows mapping _ scope image loadBase
    base offS budget 366 catalogue (by omega) page (aligned 366) _ (stateAt real e 366) i366 ob8 (RtDit.Release.z_classE tail8))
  have z367 := ev_succ (DefaultHeapShimZ.shim_z real spec config rows mapping _ scope image loadBase
    base offS budget 367 catalogue (by omega) page (aligned 367) _ (stateAt real e 367) i367 ob9 (RtDit.Release.z_class (NativeShimTails.msrDit9_tailVAt real _ prof9) rfl))
  have z368 := ev_succ (DefaultHeapShimZ.shim_ret_z real spec config rows mapping _ scope image loadBase
    separated base offS budget 368 catalogue (by omega) page (aligned 368) nodup (stateAt real e 368)
    i368 (by rw [lr368]; exact low) (lr368.trans target) ob10)
  exact z368.trans (z367.trans (z366.trans z365))

#print axioms epilogue_z

end ReleaseProfile.DefaultHeapShimFactory
