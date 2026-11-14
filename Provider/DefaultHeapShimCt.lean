import RtDit6.ShimPre
import DefaultHeapShimClass
import DefaultHeapShimTrace
import DefaultHeapShimPrologueEvents
import DefaultHeapShimEpilogueEvents
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
namespace ReleaseProfile.DefaultHeapShimFactory
open DefaultHeapShimPre
open NativeMteTagCheck
open RtDit.Release
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts
open ArmBridge.CruxGenGuarded.Release (shimPC shimData shimMap ShimPrologue ShimEpilogue)

theorem ct (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)

    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (e1 e2 : NativeState)
    (room : (357 + 12) ≤ budget) (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC j) (offPost : ∀ j, (357 + 8) ≤ j → j ≤ (357 + 11) → offS j = shimPC (j - (357 + 1)))

    (codeSlot : ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (inv01 : DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins)
      scope image loadBase base offS budget 0 catalogue e1)
    (entryRows1 : TagStatusRows e1 (e1.choiceOcc.getD 1354 0) 112)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry1 : NativeEntryAdapters.MrsDit.Profile e1)
    (isbEntry1 : NativeEntryAdapters.IsbSy.Profile e1)
    (residue1 : RtBl.CallerInv.CallerResidue e1)
    (slotE1 : RtShim.SlotPrem.ShimSlotPresent pins mapping e1)
    (spE1 : e1.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (E1 : NativeBodyDeploy.BodyEntry spec mapping base pins scope offS e1)
    (codeStore : ImageTableSeparated scope base mapping (Residue.StoreBytes pins mapping))
    (slotStore : ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → ¬ Residue.StoreBytes pins mapping a)
    (low1 : (e1.regs.gpr[30]'(by decide)).toNat < 2 ^ 55)
    (target1 : e1.regs.gpr[30]'(by decide) = base + offS 369)
    (inv02 : DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins)
      scope image loadBase base offS budget 0 catalogue e2)
    (entryRows2 : TagStatusRows e2 (e2.choiceOcc.getD 1354 0) 112)
    (mrsEntry2 : NativeEntryAdapters.MrsDit.Profile e2)
    (isbEntry2 : NativeEntryAdapters.IsbSy.Profile e2)
    (residue2 : RtBl.CallerInv.CallerResidue e2)
    (slotE2 : RtShim.SlotPrem.ShimSlotPresent pins mapping e2)
    (spE2 : e2.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (E2 : NativeBodyDeploy.BodyEntry spec mapping base pins scope offS e2)
    (low2 : (e2.regs.gpr[30]'(by decide)).toNat < 2 ^ 55)
    (target2 : e2.regs.gpr[30]'(by decide) = base + offS 369) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
      (stateAt real e1 369) (stateAt real e2 369) := by
  obtain ⟨pc1, ev1⟩ := trace real spec config rows mapping pins scope image loadBase base offS
    budget catalogue e1 room aligned offPre offPost codeSlot inv01 entryRows1 shimStatic himage hload
    mrsEntry1 isbEntry1 residue1 slotE1 spE1 static spAligned E1 codeStore slotStore low1 target1
  obtain ⟨pc2, ev2⟩ := trace real spec config rows mapping pins scope image loadBase base offS
    budget catalogue e2 room aligned offPre offPost codeSlot inv02 entryRows2 shimStatic himage hload
    mrsEntry2 isbEntry2 residue2 slotE2 spE2 static spAligned E2 codeStore slotStore low2 target2
  refine PhasedCT.phased_records (stateAt real e1) (stateAt real e2) (fun _ _ _ => True)
    369 trivial ((pc1 0 (by decide)).trans (pc2 0 (by decide)).symm) ?_
  intro j hj _
  exact ⟨StepEvents.pair spec mapping (records spec pins j) _ _ _ _ (ev1 j hj) (ev2 j hj)
    ((pc1 j (by omega)).trans (pc2 j (by omega)).symm)
    ((pc1 (j + 1) (by omega)).trans (pc2 (j + 1) (by omega)).symm), trivial⟩

#print axioms ct
end ReleaseProfile.DefaultHeapShimFactory
