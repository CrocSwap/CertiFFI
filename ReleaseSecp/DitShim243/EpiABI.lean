import DitShim243.EpiFactory
import DitShim243.ShimFrames
import DitShim243.ShimMemoryFrames
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts NativeMteTagCheck TranslateSpan ReleaseProfile
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace DitShim243.EpiABI
open Utils Geometry RtDit.Shim

theorem preserves (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (start : Nat) (imm : BitVec 26) (scope : Nat → Prop) (image : MemReloc.Image)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (e saved : NativeState)
    (invs : ∀ j, L + 8 ≤ j → j ≤ L + 12 → DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget j catalogue (stateAt real e j))
    (runs : ∀ j, L + 8 ≤ j → j ≤ L + 11 → modelStep real (stateAt real e j) = .ok () (stateAt real e (j+1)))
    (prefixControl : RtPremC.CtlRel spec e (stateAt real e (L + 8)))
    (epiControl : ∀ j, L + 8 ≤ j → j ≤ L + 12 → RtPremC.CtlRel spec (stateAt real e (L + 8)) (stateAt real e j))
    (room : L + 12 ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, j < L + 12 → (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC start j)
    (offPost : ∀ j, L + 8 ≤ j → j ≤ L + 11 → offS j = shimPC start (j - (L + 1)))
    (code : Fetch.CodeFacts spec mapping m scope image base start (Fetches.word imm))
    (slotPerm : SlotMem.SlotPerm m pins)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (slotAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e) (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (rowsStart : TagStatusRows (stateAt real e (L + 8)) ((stateAt real e (L + 8)).choiceOcc.getD 1354 0) 1)
    (spStart : (stateAt real e (L + 8)).regs.SP_EL0 = BitVec.ofNat 64 pins.sp)
    (slotStart : SlotHas pins mapping (ArmCertMem.StpEval.stpData saved 9#5 30#5) (stateAt real e (L + 8)))
    (low : saved.regs.gpr[30].toNat < 2 ^ 55)
    (retLR : (stateAt real e (L + 11)).regs.gpr[30] = saved.regs.gpr[30]) :
    ShimABI.Fields (stateAt real e (L + 8)) (stateAt real e (L + 12)) := by
  let fetches := Fetches.of_static L spec config rows mapping m scope image base offS budget catalogue start imm code offPre offPost
  have straight : ∀ j, L + 8 ≤ j → j ≤ L + 10 → offS (j+1) = offS j + 4#64 := by
    intro j lo hi
    rw [offPost (j+1) (by omega) (by omega),offPost j lo (by omega),
      show j + 1 - (L + 1) = (j - (L + 1)) + 1 by omega]
    exact shimPC_succ start _
  have presentStart : RtShim.SlotPrem.ShimSlotPresent pins mapping (stateAt real e (L + 8)) := by
    intro n hn i hi
    rw [slotStart n hn i hi]; rfl
  have f0 := ShimMemoryFrames.memory_step real spec config rows mapping m scope image base code.separated
    base offS budget pins (L+8) catalogue (by omega) page (aligned (L+8) (by omega)) _ (invs (L+8) (by omega) (by omega))
    rowsStart presentStart spStart (fun _ => False) (fun _ _ _ _ h => h) (SlotMem.LoadPay pins mapping 9#5 30#5)
    (fun _ _ _ memory pay => SlotMem.load_pay_of_fetch memory pay) _ nodup _ _ _ _
    (by decide) (by decide) (by decide) (by decide)
    (SlotMem.shim_ldp real spec config rows mapping slotPerm static slotAligned 9#5 30#5
      (by decide) (by decide) (by decide) (by decide) catalogue _)
    (next_placed (invs (L+8) (by omega) (by omega)).v1.pc (straight (L+8) (by omega) (by omega)))
    (fetches.ob365 _ (invs (L+8) (by omega) (by omega))) (stateAt real e ((L+8)+1))
    (runs (L+8) (by omega) (by omega))
  have prof9 := Profiles.msr mrsEntry isbEntry
    (Profiles.features (prefixControl.trans (epiControl (L+10) (by omega) (by omega))))
  have f1 := ShimFrames.class_step real spec config rows mapping m scope image base base offS budget catalogue (L+9)
    (by omega) page (aligned (L+9) (by omega)) (stateAt real e (L+9)) (stateAt real e ((L+9)+1)) (invs (L+9) (by omega) (by omega)) _ _ _ _ _
    (classE_toV (Choice.tail8 real (stateAt real e (L+9)))) (by decide) (by decide) (by decide)
    (fetches.ob8 _ (invs (L+9) (by omega) (by omega))) (runs (L+9) (by omega) (by omega))
  have f2 := ShimFrames.class_step real spec config rows mapping m scope image base base offS budget catalogue (L+10)
    (by omega) page (aligned (L+10) (by omega)) (stateAt real e (L+10)) (stateAt real e ((L+10)+1)) (invs (L+10) (by omega) (by omega)) _ _ _ _ _
    (NativeShimTails.msrDit9_tailVAt real (stateAt real e (L+10)) prof9) (by decide) (by decide) (by decide)
    (fetches.ob9 _ (invs (L+10) (by omega) (by omega))) (runs (L+10) (by omega) (by omega))
  have f3 := ShimFrames.ret_step real spec config rows mapping m scope image base base offS budget catalogue (L+11)
    (by omega) page (aligned (L+11) (by omega)) (stateAt real e (L+11)) (stateAt real e ((L+11)+1)) (invs (L+11) (by omega) (by omega)) 30#5 (by decide) (by decide)
    (by change (stateAt real e (L+11)).regs.gpr[30].toNat < 2^55; rw [retLR]; exact low)
    (fetches.ob10 _ (invs (L+11) (by omega) (by omega))) (runs (L+11) (by omega) (by omega))
  exact ShimFrames.trans (ShimFrames.trans (ShimFrames.trans f0 f1) f2) f3

#print axioms preserves
end DitShim243.EpiABI
