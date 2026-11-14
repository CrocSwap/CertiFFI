import RtDit6.ShimPre
import DefaultHeapShimClass
import DefaultHeapShimZPhases
import DefaultHeapBodyResidue
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

theorem frame (real : Type) [Sail.SailReal real]
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
    (target : e.regs.gpr[30]'(by decide) = base + offS 369) :
    (∀ r ∈ Residue.frameRegs, RegBind.regVal (stateAt real e 369) (.x r) = RegBind.regVal e (.x r)) ∧
    (stateAt real e 369).regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = e.regs.gpr[19]'(by decide) ∧
    (stateAt real e 369).regs.gpr[30]'(by decide) = e.regs.gpr[30]'(by decide) ∧
    (stateAt real e 369).regs.SP_EL0 = e.regs.SP_EL0 ∧
    (stateAt real e 369).regs._Z = e.regs._Z ∧
    (∀ a, ¬ Residue.StoreBytes pins mapping a → (stateAt real e 364).mem[a]? = (stateAt real e 7).mem[a]?) ∧
    (∀ i : Fin 18, RegBind.regVal (stateAt real e 364) (.x (Fin.castLE (by decide) i)) = 0#64) ∧
    (stateAt real e 364).regs.PSTATE.Z = 1#1 ∧ Release.ResidueNCV real e := by
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
  obtain ⟨_, _, lrFinal, _, spFinal, _, _, keepPost, _, _⟩ :=
    epilogue real spec config rows mapping pins scope (HeapV2.image base) base shimStatic.separated
      base offS budget catalogue e (stateAt real e 3) room page aligned straight nodup static spAligned
      inv365 mrsEntry isbEntry bodyControl shimStatic rfl rfl offPre offPost rows365 sp365 slot365
      (by rw [pre.x30_3]; exact low) (pre.x30_3.trans target)
  have preZ := prologue_z real spec config rows mapping pins scope image loadBase base offS budget
    catalogue 112 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  have epiZ := epilogue_z real spec config rows mapping pins scope (HeapV2.image base) base
    shimStatic.separated base offS budget catalogue e (stateAt real e 3) room page aligned straight
    nodup static spAligned inv365 mrsEntry isbEntry bodyControl shimStatic rfl rfl offPre offPost
    rows365 sp365 slot365 (by rw [pre.x30_3]; exact low) (pre.x30_3.trans target)
  have dp := DefaultHeapRun.body_deployment_of_prologue real 357 spec config rows mapping base pins
    scope offS budget (budget - 7) e catalogue 112 E rfl
    (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) rowRoom) pre
  have index357 : stateAt real e 364 = stateAt real (stateAt real e 7) 357 :=
    RtDit.Window.stateAt_add real e 7 357
  have index358 : stateAt real e 365 = stateAt real (stateAt real e 7) 358 :=
    RtDit.Window.stateAt_add real e 7 358
  have inv357 := DefaultHeapRun.prefixes real spec config rows mapping base pins (stateAt real e 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp (by omega) 357 (by decide)
  obtain ⟨_, bodyFrame, _, bodyX19, _, _⟩ := DefaultHeapRun.body_abi real spec config rows mapping base pins
    (stateAt real e 7) (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws
    dp (by omega) (by rw [pre.x30_7]; exact bodyLow)
  rw [← index358] at bodyFrame bodyX19
  obtain ⟨fin, retRun, _, _, _, _, retZ, _, _⟩ := DefaultHeapRun.body_ret real spec config rows mapping
    base pins (stateAt real e 7) (budget - 7) catalogue DefaultHeapBudget.capacity
    DefaultHeapBudget.prefixDraws dp (by omega) (by rw [pre.x30_7]; exact bodyLow)
  have sameFin : stateAt real e 365 = fin := by
    rw [index358]
    exact EvSteps.stateAt_succ_of retRun
  rw [← sameFin, ← index357] at retZ
  have bodyZ := DefaultHeapRun.body_z real spec config rows mapping base pins (stateAt real e 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp (by omega) 357 (by decide)
  have scrub := DefaultHeapRun.body_scrub real spec config rows mapping base pins (stateAt real e 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp (by omega)
  have flags := DefaultHeapRun.body_nzcv real spec config rows mapping base pins (stateAt real e 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp (by omega)
  have memFrame := inv357.2.1.2
  rw [← index357] at bodyZ scrub flags memFrame
  have flagFields : (stateAt real e 364).regs.PSTATE.N = 0#1 ∧
      (stateAt real e 364).regs.PSTATE.Z = 1#1 ∧
      (stateAt real e 364).regs.PSTATE.C = 0#1 ∧ (stateAt real e 364).regs.PSTATE.V = 0#1 := by
    simpa only [Flags.nzcv, Prod.mk.injEq] using flags
  have safe : ∀ r ∈ Residue.frameRegs, r.val ≠ 9 ∧ r.val ≠ 30 := by decide
  refine ⟨?_, ?_, lrFinal.trans pre.x30_3, ?_, epiZ.trans (retZ.trans (bodyZ.trans preZ)),
    memFrame, scrub, flagFields.2.1, ?_⟩
  · intro r hr
    simp only [RegBind.regVal] at bodyFrame ⊢
    rw [keepPost r (safe r hr).1 (safe r hr).2]
    exact (bodyFrame r hr).trans (pre.keepPre r (safe r hr).1 (safe r hr).2)
  · change (stateAt real e 369).regs.gpr[19]'(by decide) = e.regs.gpr[19]'(by decide)
    rw [keepPost ⟨19, by decide⟩ (by decide) (by decide)]
    have bx19 : (stateAt real e 365).regs.gpr[19]'(by decide) =
        (stateAt real e 7).regs.gpr[19]'(by decide) := bodyX19
    exact bx19.trans (pre.keepPre ⟨19, by decide⟩ (by decide) (by decide))
  · rw [spFinal, sp365, spE]
  · exact ⟨flagFields.1, flagFields.2.2.1, flagFields.2.2.2⟩

#print axioms frame
end ReleaseProfile.DefaultHeapShimFactory
