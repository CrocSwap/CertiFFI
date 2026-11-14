-- F21 (CertiFFI): physical variant of DefaultHeapShimInitialFunctional.functional (no dbl/inj/inputNoSlot).
import RtDit6.ShimPre
import DefaultHeapShimClass
import DefaultHeapShimFactory
import DefaultHeapShimEpilogueFactory
import DefaultHeapShimBody
import DefaultHeapFunctional
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
import DefaultHeapF21Functional
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

theorem functionalP (real : Type) [Sail.SailReal real]
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
    (target : e.regs.gpr[30]'(by decide) = base + offS 369)
    (ndPA : TranslateMem.NoDoubleMapPA pins mapping) (ndSlot : TranslateMem.NoDoubleMapSlot pins mapping)
    (hd : TranslateMem.RegionsDisjoint pins)
    (slotDisj : pins.x1 + 32 ≤ pins.sp ∨ pins.sp + 16 ≤ pins.x1) (spHi : pins.sp + 16 ≤ 2 ^ 64) :
    Release.Functional mapping pins e (stateAt real e 369) := by
  have page := E.S.page
  have nodup := E.S.nodup
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    decide
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.S.low
  have bodyLow : (base + offS 365).toNat < 2 ^ 55 := by
    rw [offPost 365 (by decide) (by decide)]
    exact low_of _ (by decide) E.S.low
  obtain ⟨pre, _⟩ := prologue real spec config rows mapping pins scope image loadBase base offS
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
  obtain ⟨_, _, _, _, _, epiMem, _, keepPost, _, _⟩ :=
    epilogue real spec config rows mapping pins scope (HeapV2.image base) base shimStatic.separated
      base offS budget catalogue e (stateAt real e 3) room page aligned straight nodup static spAligned
      inv365 mrsEntry isbEntry bodyControl shimStatic rfl rfl offPre offPost rows365 sp365 slot365
      (by rw [pre.x30_3]; exact low) (pre.x30_3.trans target)
  have dp := DefaultHeapRun.body_deployment_of_prologue real 357 spec config rows mapping base pins
    scope offS budget (budget - 7) e catalogue 112 E rfl
    (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) rowRoom) pre
  obtain ⟨fin, run, _, gpr, _, mem, _, _, _⟩ :=
    DefaultHeapRun.body_ret real spec config rows mapping base pins (stateAt real e 7)
      (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp
      (Nat.le_sub_of_add_le bodyRoom) (by rw [pre.x30_7]; exact bodyLow)
  have sameFin : stateAt real e 365 = fin := by
    rw [RtDit.Window.stateAt_add real e 7 358]
    exact EvSteps.stateAt_succ_of run
  rw [← sameFin, ← RtDit.Window.stateAt_add real e 7 357] at gpr mem
  have inputNoSlot : ∀ i, i < 32 → ∀ n, mapping (BitVec.ofNat 64 (pins.x1 + i)) = some n →
      ¬ RtShim2.ShimMem.slotBytes pins mapping n :=
    ArmCertValue.HeapV2PlanP.slotSep_of_walkP pins mapping hd (dp.pinAligned 0)
      (ReleaseProfile.DefaultHeapF21.accessLeaf_of_cdp dp)
      (TranslateMem.slotLeaf_of_closed pins inv0.closed (acc := TranslateMem.dataAcc false) (aligned := true) (size := 16)
        (Or.inr (Or.inr ⟨false, rfl, rfl, TranslateMem.dataAcc_shape _⟩)))
      ndSlot slotDisj spHi
  have inputFrame : ∀ i, i < 32 → Release.bufByte mapping (stateAt real e 7) pins.x1 i =
      Release.bufByte mapping e pins.x1 i := by
    intro i within
    simp only [Release.bufByte]
    cases mapped : mapping (BitVec.ofNat 64 (pins.x1 + i)) with
    | none => simp only [mapped, Option.bind_none]
    | some n =>
      simp only [mapped, Option.bind_some]
      exact pre.memPre n (inputNoSlot i within n mapped)
  have outputFrame : ∀ i, i < 32 → Release.bufByte mapping (stateAt real e 369) pins.x0 i =
      Release.bufByte mapping (stateAt real e 364) pins.x0 i := by
    intro i within
    simp only [Release.bufByte]
    cases mapped : mapping (BitVec.ofNat 64 (pins.x0 + i)) with
    | none => simp only [mapped, Option.bind_none]
    | some n =>
      simp only [mapped, Option.bind_some]
      exact (epiMem n).trans (congrArg (fun memory => memory[n]?) mem)
  exact ReleaseProfile.DefaultHeapRunP.shim_functionalP real spec config rows mapping base pins e (budget - 7)
    catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp
    (Nat.le_trans (by decide : 357 ≤ 358) (Nat.le_sub_of_add_le bodyRoom)) hd ndPA inputFrame outputFrame
    (by simpa only [gpr] using keepPost ⟨0, by decide⟩ (by decide) (by decide))

end ReleaseProfile.DefaultHeapShimFactory
