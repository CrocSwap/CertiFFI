import DitShim243.Factory
import DitShim243.ShimFrames
import DitShim243.ShimMemoryFrames
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts NativeMteTagCheck TranslateSpan ReleaseProfile
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace DitShim243.PreABI
open Utils Geometry

theorem preserves (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (start : Nat) (imm : BitVec 26) (scope : Nat → Prop) (image : MemReloc.Image)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (capacity : Nat) (e : NativeState)
    (pre : Pre.ShimPreMG real L spec config rows mapping pins m start scope image base base offS budget catalogue capacity e)
    (room : L + 12 ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, j < L + 12 → (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC start j)
    (offPost : ∀ j, L + 8 ≤ j → j ≤ L + 11 → offS j = shimPC start (j - (L + 1)))
    (code : Fetch.CodeFacts spec mapping m scope image base start (Fetches.word imm))
    (slotPerm : SlotMem.SlotPerm m pins)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (slotAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)
    (codeSlot : ImageTableSeparated scope base mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (rowRoom : 2 ≤ capacity)
    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e) (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (land : offS 6 + sign_extend (imm ++ 0#2) 64 = offS 7)
    (low : (base + offS 7).toNat < 2 ^ 55) :
    ∀ k, k ≤ 7 → ShimABI.Fields e (stateAt real e k) := by
  let fetches := Fetches.of_static L spec config rows mapping m scope image base offS budget catalogue start imm code offPre offPost
  have prof2 := Profiles.mrs mrsEntry (Profiles.features (pre.controlPrefix 2 (by omega)))
  have prof4 := Profiles.dit_on mrsEntry (Profiles.features (pre.controlPrefix 4 (by omega)))
  have prof5 := Profiles.isb isbEntry (Profiles.features (pre.controlPrefix 5 (by omega)))
  have f0 := ShimFrames.class_step real spec config rows mapping m scope image base base offS budget catalogue 0
    (by omega) page (aligned 0 (by omega)) (stateAt real e 0) (stateAt real e (0+1)) (pre.inv 0 (by omega)) _ _ _ _ _
    (NativeShimTails.btiC_tailVAt real e) (by decide) (by decide) (by decide) (fetches.ob0 _ (pre.inv 0 (by omega))) (pre.runs 0 (by omega))
  have f1 := ShimFrames.class_step real spec config rows mapping m scope image base base offS budget catalogue 1
    (by omega) page (aligned 1 (by omega)) (stateAt real e 1) (stateAt real e (1+1)) (pre.inv 1 (by omega)) _ _ _ _ _
    (classE_toV (Choice.tail1 real (stateAt real e 1))) (by decide) (by decide) (by decide) (fetches.ob1 _ (pre.inv 1 (by omega))) (pre.runs 1 (by omega))
  have f2 := ShimFrames.class_step real spec config rows mapping m scope image base base offS budget catalogue 2
    (by omega) page (aligned 2 (by omega)) (stateAt real e 2) (stateAt real e (2+1)) (pre.inv 2 (by omega)) _ _ _ _ _
    (NativeShimTails.mrsDit9_tailVAt real (stateAt real e 2) prof2) (by decide) (by decide) (by decide) (fetches.ob2 _ (pre.inv 2 (by omega))) (pre.runs 2 (by omega))
  have f4 := ShimFrames.class_step real spec config rows mapping m scope image base base offS budget catalogue 4
    (by omega) page (aligned 4 (by omega)) (stateAt real e 4) (stateAt real e (4+1)) (pre.inv 4 (by omega)) _ _ _ _ _
    (NativeShimTails.ditOn_tailVAt real (stateAt real e 4) prof4) (by decide) (by decide) (by decide) (fetches.ob4 _ (pre.inv 4 (by omega))) (pre.runs 4 (by omega))
  have f5 := ShimFrames.class_step real spec config rows mapping m scope image base base offS budget catalogue 5
    (by omega) page (aligned 5 (by omega)) (stateAt real e 5) (stateAt real e (5+1)) (pre.inv 5 (by omega)) _ _ _ _ _
    (NativeShimTails.isbSy_tailVAt real (stateAt real e 5) prof5) (by decide) (by decide) (by decide) (fetches.ob5 _ (pre.inv 5 (by omega))) (pre.runs 5 (by omega))
  obtain ⟨used,delta,bound⟩ := pre.choicePrefix 3 (by omega)
  have rows3 := DefaultMTE2.rows_after_delta e (stateAt real e 3) capacity 1 used pre.statusRows delta (by omega)
  have straight3 : offS (3 + 1) = offS 3 + 4#64 := by rw [offPre 4 (by omega),offPre 3 (by omega)]; exact shimPC_succ start 3
  have f3 := ShimMemoryFrames.memory_step real spec config rows mapping m scope image base code.separated
    base offS budget pins 3 catalogue (by omega) page (aligned 3 (by omega)) _ (pre.inv 3 (by omega)) rows3 pre.slot3 pre.sp3
    _ codeSlot (SlotMem.StorePay pins mapping 9#5 30#5)
    (fun _ _ g _ pay => SlotMem.store_pay_of_fetch g pay) _ nodup _ _ _ []
    (by decide) (by decide) (by decide) (by decide)
    (SlotMem.shim_stp real spec config rows mapping slotPerm static slotAligned 9#5 30#5
      (by decide) (by decide) (by decide) catalogue _)
    (next_placed (pre.inv 3 (by omega)).v1.pc straight3) (fetches.ob3 _ (pre.inv 3 (by omega)))
    (stateAt real e (3+1)) (pre.runs 3 (by omega))
  have target : NativeEntryCallerParts.blTarget imm (stateAt real e 6) = base + offS 7 := by
    rw [NativeEntryCallerRegisters.bl_target,(pre.inv 6 (by omega)).v1.pc,BitVec.add_assoc,land]
  have f6 := ShimFrames.bl_step real spec config rows mapping m scope image base base offS budget catalogue 6
    (by omega) page (aligned 6 (by omega)) (stateAt real e 6) (stateAt real e (6+1)) (pre.inv 6 (by omega)) imm pre.caller6 (by rw [target]; exact low)
    (fetches.ob6 _ (pre.inv 6 (by omega))) (pre.runs 6 (by omega))
  have allSteps : ∀ j, j ≤ 6 → ShimABI.Fields (stateAt real e j) (stateAt real e (j+1)) := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact f0
    · exact f1
    · exact f2
    · exact f3
    · exact f4
    · exact f5
    · exact f6
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl,rfl,rfl,rfl⟩
  | succ j ih =>
    intro bound
    exact ShimFrames.trans (ih (by omega)) (allSteps j (by omega))

#print axioms preserves
end DitShim243.PreABI
