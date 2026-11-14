import RtDit6.ShimPre
import DefaultHeapShimClass
import DefaultHeapTrapEntry
import DefaultHeapTrapValueRun
import DefaultHeapShimPrologueEvents
import DefaultHeapShimFactory
import DefaultHeapShimEpilogueFactory
import DefaultHeapShimBody
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
namespace ReleaseProfile.DefaultHeapTrap
open DefaultHeapShimPre
open HeapV2StepCerts.ValBind
open NativeMteTagCheck
open RtDit.Release
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts
open ArmBridge.CruxGenGuarded.Release (shimPC shimData shimMap ShimPrologue ShimEpilogue)

def offsets (L : Nat) (offS : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  if j ≤ 6 then offS j else RtBl.Trap.trapOff L (j - 7)

def records {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins)
    (j : Nat) : List (Option ArmCertCTOrdered.OrderedEventV2.Record) :=
  if j ≤ 6 then Release.shimData spec pins j else []

theorem initial_0 (real : Type) [Sail.SailReal real]
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
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) 1)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (tableRows : NativeSourceInit.Plan)
    (E : NativeBodyDeploy.TrapEntryM spec mapping
      (HeapV2E17.consumerMapOn HeapV2E17.noData pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      base pins scope offS e rows tableRows)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (np : TrapPath 1 pins (qOf e)) :
    (∀ j, j ≤ 8 → (stateAt real e j).regs._PC = base + offsets 1 offS j) ∧
    (∀ j, j < 8 → StepEvents.EvShape spec mapping (records spec pins j)
      (stateAt real e j) (stateAt real e (j + 1))) ∧
    (stateAt real e 8).regs._PC = base + RtBl.Trap.trapOffset ∧
    (∀ j, 5 ≤ j → j ≤ 7 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (∀ k, k ≤ 1 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees
      (HeapV2E17.consumerMapOn HeapV2E17.noData pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      (stateAt real e (7 + k))) := by
  have page := E.page
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    decide
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.low
  obtain ⟨pre, _⟩ := DefaultHeapShimFactory.prologue real spec config rows mapping pins scope image loadBase
    base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  obtain ⟨preInv, preEv⟩ := DefaultHeapShimFactory.prologue_events real spec config rows mapping pins scope
    image loadBase base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0
    entryRows shimStatic himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  rw [himage, hload] at pre
  have R := DefaultHeapRun.prologue_run_facts real 357 spec config rows mapping base pins scope offS budget
    e catalogue 1 pre
  have initial := body_deployment spec config rows mapping HeapV2E17.noData base pins scope offS budget
    (budget - 7) e catalogue tableRows E (fun _ h => NativeBodyDeploy.closed_trap_of_shimMap h) rfl _ pre.inv7 R
  have np7 : TrapPath 1 pins (qOf (stateAt real e 7)) := by
    rw [R.q]
    exact np
  obtain ⟨body, trapPC, bodyEv⟩ := trap0_runT real spec config rows mapping base (budget - 7) pins
    (rowsFootprint spec.imageRows).byte HeapV2E17.noData catalogue (stateAt real e 7) E.static nodup E.agrees
    (by omega) page (low_of _ (by decide) E.low) (qOf (stateAt real e 7)) np7 initial
    (ValBind.initialT_1 (stateAt real e 7))
  have index (k : Nat) : stateAt real e (7 + k) = stateAt real (stateAt real e 7) k :=
    RtDit.Window.stateAt_add real e 7 k
  refine ⟨?_, ?_, ?_, pre.ditOn, ?_⟩
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [offsets, ite_eq_left early] using (preInv j (by omega)).v1.pc
    · have pc := (body (j - 7) (by omega)).1.1.core.v1.pc
      rw [← index, show 7 + (j - 7) = j by omega] at pc
      simpa only [offsets, ite_eq_right early] using pc
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [records, ite_eq_left early] using preEv j early
    · have ev := bodyEv (j - 7) (by omega)
      rw [← index, ← index] at ev
      simpa only [records, ite_eq_right early, show 7 + (j - 7) = j by omega,
        show 7 + (j - 7 + 1) = j + 1 by omega] using ev
  · rw [← index] at trapPC
    exact trapPC
  · intro k hk
    rw [index]
    exact (body k hk).2

#print axioms initial_0

theorem initial_1 (real : Type) [Sail.SailReal real]
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
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) 1)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (tableRows : NativeSourceInit.Plan)
    (E : NativeBodyDeploy.TrapEntryM spec mapping
      (HeapV2E17.consumerMapOn HeapV2E17.noData pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      base pins scope offS e rows tableRows)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (np : TrapPath 2 pins (qOf e)) :
    (∀ j, j ≤ 9 → (stateAt real e j).regs._PC = base + offsets 2 offS j) ∧
    (∀ j, j < 9 → StepEvents.EvShape spec mapping (records spec pins j)
      (stateAt real e j) (stateAt real e (j + 1))) ∧
    (stateAt real e 9).regs._PC = base + RtBl.Trap.trapOffset ∧
    (∀ j, 5 ≤ j → j ≤ 7 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (∀ k, k ≤ 2 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees
      (HeapV2E17.consumerMapOn HeapV2E17.noData pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      (stateAt real e (7 + k))) := by
  have page := E.page
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    decide
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.low
  obtain ⟨pre, _⟩ := DefaultHeapShimFactory.prologue real spec config rows mapping pins scope image loadBase
    base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  obtain ⟨preInv, preEv⟩ := DefaultHeapShimFactory.prologue_events real spec config rows mapping pins scope
    image loadBase base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0
    entryRows shimStatic himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  rw [himage, hload] at pre
  have R := DefaultHeapRun.prologue_run_facts real 357 spec config rows mapping base pins scope offS budget
    e catalogue 1 pre
  have initial := body_deployment spec config rows mapping HeapV2E17.noData base pins scope offS budget
    (budget - 7) e catalogue tableRows E (fun _ h => NativeBodyDeploy.closed_trap_of_shimMap h) rfl _ pre.inv7 R
  have np7 : TrapPath 2 pins (qOf (stateAt real e 7)) := by
    rw [R.q]
    exact np
  obtain ⟨body, trapPC, bodyEv⟩ := trap1_runT real spec config rows mapping base (budget - 7) pins
    (rowsFootprint spec.imageRows).byte HeapV2E17.noData catalogue (stateAt real e 7) E.static nodup E.agrees
    (by omega) page (low_of _ (by decide) E.low) (qOf (stateAt real e 7)) np7 initial
    (ValBind.initialT_2 (stateAt real e 7))
  have index (k : Nat) : stateAt real e (7 + k) = stateAt real (stateAt real e 7) k :=
    RtDit.Window.stateAt_add real e 7 k
  refine ⟨?_, ?_, ?_, pre.ditOn, ?_⟩
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [offsets, ite_eq_left early] using (preInv j (by omega)).v1.pc
    · have pc := (body (j - 7) (by omega)).1.1.core.v1.pc
      rw [← index, show 7 + (j - 7) = j by omega] at pc
      simpa only [offsets, ite_eq_right early] using pc
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [records, ite_eq_left early] using preEv j early
    · have ev := bodyEv (j - 7) (by omega)
      rw [← index, ← index] at ev
      simpa only [records, ite_eq_right early, show 7 + (j - 7) = j by omega,
        show 7 + (j - 7 + 1) = j + 1 by omega] using ev
  · rw [← index] at trapPC
    exact trapPC
  · intro k hk
    rw [index]
    exact (body k hk).2

#print axioms initial_1

theorem initial_2 (real : Type) [Sail.SailReal real]
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
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) 1)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (tableRows : NativeSourceInit.Plan)
    (E : NativeBodyDeploy.TrapEntryM spec mapping
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      base pins scope offS e rows tableRows)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (np : TrapPath 4 pins (qOf e)) :
    (∀ j, j ≤ 11 → (stateAt real e j).regs._PC = base + offsets 4 offS j) ∧
    (∀ j, j < 11 → StepEvents.EvShape spec mapping (records spec pins j)
      (stateAt real e j) (stateAt real e (j + 1))) ∧
    (stateAt real e 11).regs._PC = base + RtBl.Trap.trapOffset ∧
    (∀ j, 5 ≤ j → j ≤ 7 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (∀ k, k ≤ 4 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      (stateAt real e (7 + k))) := by
  have page := E.page
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    decide
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.low
  obtain ⟨pre, _⟩ := DefaultHeapShimFactory.prologue real spec config rows mapping pins scope image loadBase
    base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  obtain ⟨preInv, preEv⟩ := DefaultHeapShimFactory.prologue_events real spec config rows mapping pins scope
    image loadBase base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0
    entryRows shimStatic himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  rw [himage, hload] at pre
  have R := DefaultHeapRun.prologue_run_facts real 357 spec config rows mapping base pins scope offS budget
    e catalogue 1 pre
  have initial := body_deployment spec config rows mapping (fun _ => True) base pins scope offS budget
    (budget - 7) e catalogue tableRows E (fun _ h => closed_all_of_shimMap h) rfl _ pre.inv7 R
  have np7 : TrapPath 4 pins (qOf (stateAt real e 7)) := by
    rw [R.q]
    exact np
  obtain ⟨body, trapPC, bodyEv⟩ := trap2_runT real spec config rows mapping base (budget - 7) pins
    (rowsFootprint spec.imageRows).byte (fun _ => True) catalogue (stateAt real e 7) E.static nodup E.agrees
    (by omega) page (low_of _ (by decide) E.low) (qOf (stateAt real e 7)) np7 initial
    (ValBind.initialT_4 (stateAt real e 7))
  have index (k : Nat) : stateAt real e (7 + k) = stateAt real (stateAt real e 7) k :=
    RtDit.Window.stateAt_add real e 7 k
  refine ⟨?_, ?_, ?_, pre.ditOn, ?_⟩
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [offsets, ite_eq_left early] using (preInv j (by omega)).v1.pc
    · have pc := (body (j - 7) (by omega)).1.1.core.v1.pc
      rw [← index, show 7 + (j - 7) = j by omega] at pc
      simpa only [offsets, ite_eq_right early] using pc
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [records, ite_eq_left early] using preEv j early
    · have ev := bodyEv (j - 7) (by omega)
      rw [← index, ← index] at ev
      simpa only [records, ite_eq_right early, show 7 + (j - 7) = j by omega,
        show 7 + (j - 7 + 1) = j + 1 by omega] using ev
  · rw [← index] at trapPC
    exact trapPC
  · intro k hk
    rw [index]
    exact (body k hk).2

#print axioms initial_2

theorem initial_3 (real : Type) [Sail.SailReal real]
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
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) 1)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (tableRows : NativeSourceInit.Plan)
    (E : NativeBodyDeploy.TrapEntryM spec mapping
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      base pins scope offS e rows tableRows)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (np : TrapPath 6 pins (qOf e)) :
    (∀ j, j ≤ 13 → (stateAt real e j).regs._PC = base + offsets 6 offS j) ∧
    (∀ j, j < 13 → StepEvents.EvShape spec mapping (records spec pins j)
      (stateAt real e j) (stateAt real e (j + 1))) ∧
    (stateAt real e 13).regs._PC = base + RtBl.Trap.trapOffset ∧
    (∀ j, 5 ≤ j → j ≤ 7 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (∀ k, k ≤ 6 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      (stateAt real e (7 + k))) := by
  have page := E.page
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    decide
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.low
  obtain ⟨pre, _⟩ := DefaultHeapShimFactory.prologue real spec config rows mapping pins scope image loadBase
    base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  obtain ⟨preInv, preEv⟩ := DefaultHeapShimFactory.prologue_events real spec config rows mapping pins scope
    image loadBase base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0
    entryRows shimStatic himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  rw [himage, hload] at pre
  have R := DefaultHeapRun.prologue_run_facts real 357 spec config rows mapping base pins scope offS budget
    e catalogue 1 pre
  have initial := body_deployment spec config rows mapping (fun _ => True) base pins scope offS budget
    (budget - 7) e catalogue tableRows E (fun _ h => closed_all_of_shimMap h) rfl _ pre.inv7 R
  have np7 : TrapPath 6 pins (qOf (stateAt real e 7)) := by
    rw [R.q]
    exact np
  obtain ⟨body, trapPC, bodyEv⟩ := trap3_runT real spec config rows mapping base (budget - 7) pins
    (rowsFootprint spec.imageRows).byte (fun _ => True) catalogue (stateAt real e 7) E.static nodup E.agrees
    (by omega) page (low_of _ (by decide) E.low) (qOf (stateAt real e 7)) np7 initial
    (ValBind.initialT_6 (stateAt real e 7))
  have index (k : Nat) : stateAt real e (7 + k) = stateAt real (stateAt real e 7) k :=
    RtDit.Window.stateAt_add real e 7 k
  refine ⟨?_, ?_, ?_, pre.ditOn, ?_⟩
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [offsets, ite_eq_left early] using (preInv j (by omega)).v1.pc
    · have pc := (body (j - 7) (by omega)).1.1.core.v1.pc
      rw [← index, show 7 + (j - 7) = j by omega] at pc
      simpa only [offsets, ite_eq_right early] using pc
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [records, ite_eq_left early] using preEv j early
    · have ev := bodyEv (j - 7) (by omega)
      rw [← index, ← index] at ev
      simpa only [records, ite_eq_right early, show 7 + (j - 7) = j by omega,
        show 7 + (j - 7 + 1) = j + 1 by omega] using ev
  · rw [← index] at trapPC
    exact trapPC
  · intro k hk
    rw [index]
    exact (body k hk).2

#print axioms initial_3

theorem initial_4 (real : Type) [Sail.SailReal real]
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
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) 1)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (tableRows : NativeSourceInit.Plan)
    (E : NativeBodyDeploy.TrapEntryM spec mapping
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      base pins scope offS e rows tableRows)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (np : TrapPath 8 pins (qOf e)) :
    (∀ j, j ≤ 15 → (stateAt real e j).regs._PC = base + offsets 8 offS j) ∧
    (∀ j, j < 15 → StepEvents.EvShape spec mapping (records spec pins j)
      (stateAt real e j) (stateAt real e (j + 1))) ∧
    (stateAt real e 15).regs._PC = base + RtBl.Trap.trapOffset ∧
    (∀ j, 5 ≤ j → j ≤ 7 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (∀ k, k ≤ 8 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      (stateAt real e (7 + k))) := by
  have page := E.page
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    decide
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.low
  obtain ⟨pre, _⟩ := DefaultHeapShimFactory.prologue real spec config rows mapping pins scope image loadBase
    base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  obtain ⟨preInv, preEv⟩ := DefaultHeapShimFactory.prologue_events real spec config rows mapping pins scope
    image loadBase base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0
    entryRows shimStatic himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  rw [himage, hload] at pre
  have R := DefaultHeapRun.prologue_run_facts real 357 spec config rows mapping base pins scope offS budget
    e catalogue 1 pre
  have initial := body_deployment spec config rows mapping (fun _ => True) base pins scope offS budget
    (budget - 7) e catalogue tableRows E (fun _ h => closed_all_of_shimMap h) rfl _ pre.inv7 R
  have np7 : TrapPath 8 pins (qOf (stateAt real e 7)) := by
    rw [R.q]
    exact np
  obtain ⟨body, trapPC, bodyEv⟩ := trap4_runT real spec config rows mapping base (budget - 7) pins
    (rowsFootprint spec.imageRows).byte (fun _ => True) catalogue (stateAt real e 7) E.static nodup E.agrees
    (by omega) page (low_of _ (by decide) E.low) (qOf (stateAt real e 7)) np7 initial
    (ValBind.initialT_8 (stateAt real e 7))
  have index (k : Nat) : stateAt real e (7 + k) = stateAt real (stateAt real e 7) k :=
    RtDit.Window.stateAt_add real e 7 k
  refine ⟨?_, ?_, ?_, pre.ditOn, ?_⟩
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [offsets, ite_eq_left early] using (preInv j (by omega)).v1.pc
    · have pc := (body (j - 7) (by omega)).1.1.core.v1.pc
      rw [← index, show 7 + (j - 7) = j by omega] at pc
      simpa only [offsets, ite_eq_right early] using pc
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [records, ite_eq_left early] using preEv j early
    · have ev := bodyEv (j - 7) (by omega)
      rw [← index, ← index] at ev
      simpa only [records, ite_eq_right early, show 7 + (j - 7) = j by omega,
        show 7 + (j - 7 + 1) = j + 1 by omega] using ev
  · rw [← index] at trapPC
    exact trapPC
  · intro k hk
    rw [index]
    exact (body k hk).2

#print axioms initial_4

theorem initial_5 (real : Type) [Sail.SailReal real]
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
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) 1)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (tableRows : NativeSourceInit.Plan)
    (E : NativeBodyDeploy.TrapEntryM spec mapping
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      base pins scope offS e rows tableRows)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (np : TrapPath 10 pins (qOf e)) :
    (∀ j, j ≤ 17 → (stateAt real e j).regs._PC = base + offsets 10 offS j) ∧
    (∀ j, j < 17 → StepEvents.EvShape spec mapping (records spec pins j)
      (stateAt real e j) (stateAt real e (j + 1))) ∧
    (stateAt real e 17).regs._PC = base + RtBl.Trap.trapOffset ∧
    (∀ j, 5 ≤ j → j ≤ 7 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (∀ k, k ≤ 10 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      (stateAt real e (7 + k))) := by
  have page := E.page
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    decide
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.low
  obtain ⟨pre, _⟩ := DefaultHeapShimFactory.prologue real spec config rows mapping pins scope image loadBase
    base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  obtain ⟨preInv, preEv⟩ := DefaultHeapShimFactory.prologue_events real spec config rows mapping pins scope
    image loadBase base offS budget catalogue 1 e room page aligned offPre offPost nodup codeSlot inv0
    entryRows shimStatic himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  rw [himage, hload] at pre
  have R := DefaultHeapRun.prologue_run_facts real 357 spec config rows mapping base pins scope offS budget
    e catalogue 1 pre
  have initial := body_deployment spec config rows mapping (fun _ => True) base pins scope offS budget
    (budget - 7) e catalogue tableRows E (fun _ h => closed_all_of_shimMap h) rfl _ pre.inv7 R
  have np7 : TrapPath 10 pins (qOf (stateAt real e 7)) := by
    rw [R.q]
    exact np
  obtain ⟨body, trapPC, bodyEv⟩ := trap5_runT real spec config rows mapping base (budget - 7) pins
    (rowsFootprint spec.imageRows).byte (fun _ => True) catalogue (stateAt real e 7) E.static nodup E.agrees
    (by omega) page (low_of _ (by decide) E.low) (qOf (stateAt real e 7)) np7 initial
    (ValBind.initialT_10 (stateAt real e 7))
  have index (k : Nat) : stateAt real e (7 + k) = stateAt real (stateAt real e 7) k :=
    RtDit.Window.stateAt_add real e 7 k
  refine ⟨?_, ?_, ?_, pre.ditOn, ?_⟩
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [offsets, ite_eq_left early] using (preInv j (by omega)).v1.pc
    · have pc := (body (j - 7) (by omega)).1.1.core.v1.pc
      rw [← index, show 7 + (j - 7) = j by omega] at pc
      simpa only [offsets, ite_eq_right early] using pc
  · intro j hj
    by_cases early : j ≤ 6
    · simpa only [records, ite_eq_left early] using preEv j early
    · have ev := bodyEv (j - 7) (by omega)
      rw [← index, ← index] at ev
      simpa only [records, ite_eq_right early, show 7 + (j - 7) = j by omega,
        show 7 + (j - 7 + 1) = j + 1 by omega] using ev
  · rw [← index] at trapPC
    exact trapPC
  · intro k hk
    rw [index]
    exact (body k hk).2

#print axioms initial_5

end ReleaseProfile.DefaultHeapTrap
