import RtDit6.ShimPre
import DefaultHeapShimClass
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

theorem run (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)

    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (e : NativeState)
    (room : (357 + 12) ≤ budget)  (aligned : ∀ j, (offS j).toNat % 4 = 0)
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
    DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope
      (HeapV2.image base) base base offS budget 369 catalogue (stateAt real e 369) ∧
    RtPremC.CtlRel spec e (stateAt real e 369) ∧
    (∃ used, ChoiceDelta e (stateAt real e 369) used ∧ used ≤ 112) ∧
    (stateAt real e 369).regs._PC = e.regs.gpr[30]'(by decide) ∧
    (stateAt real e 369).regs.gpr[30]'(by decide) = e.regs.gpr[30]'(by decide) ∧
    (stateAt real e 369).regs.SP_EL0 = e.regs.SP_EL0 ∧
    (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT := by
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
  obtain ⟨bodyControl, _, bodyTrace, rows365⟩ := DefaultHeapShimBody.body_transport real spec config rows
    mapping base pins scope offS budget e catalogue 112 E pre bodyRoom rowRoom bodyLow
  have straight : ∀ j, 365 ≤ j → j ≤ 367 → offS (j + 1) = offS j + 4#64 := by
    intro j lo hi
    rw [offPost (j + 1) (by omega) (by omega), offPost j lo (by omega),
      show j + 1 - 358 = (j - 358) + 1 by omega, shimPC_succ]
  obtain ⟨_, finalInv, lrFinal, _, spFinal, _, ditFinal, _, epiControl, epiUsed, epiChoice, epiBound⟩ :=
    epilogue real spec config rows mapping pins scope (HeapV2.image base) base shimStatic.separated
      base offS budget catalogue e (stateAt real e 3) room page aligned straight nodup static spAligned
      inv365 mrsEntry isbEntry bodyControl shimStatic rfl rfl offPre offPost rows365 sp365 slot365
      (by rw [pre.x30_3]; exact low) (pre.x30_3.trans target)
  obtain ⟨bodyUsed, bodyChoice, bodyBound⟩ := bodyTrace
  have totalBound : bodyUsed + epiUsed ≤ 112 := by
    have bound := Nat.add_le_add bodyBound epiBound
    simpa only [DefaultHeapBudget.capacity_eq] using bound
  refine ⟨finalInv, bodyControl.trans epiControl,
    ⟨bodyUsed + epiUsed, choice_delta_trans bodyChoice epiChoice, totalBound⟩,
    finalInv.v1.pc.trans target.symm, lrFinal.trans pre.x30_3, ?_, ditFinal.trans savedDit⟩
  rw [sp365] at spFinal
  exact spFinal.trans spE.symm

#print axioms run
end ReleaseProfile.DefaultHeapShimFactory
