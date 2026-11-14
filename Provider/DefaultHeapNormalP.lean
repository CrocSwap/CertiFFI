-- F21 (CertiFFI): physical variant of DefaultHeapNormal.normal (no dbl/inj/inputNoSlot).
import RtDit6.ShimPre
import DefaultHeapShimInitialFunctionalP
import DefaultHeapShimClass
import DefaultHeapShimInitial
import DefaultHeapShimInitialFunctional
import DefaultHeapShimDitWindow
import DefaultHeapShimFrame
import DefaultHeapShimE17
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

theorem normalP (real : Type) [Sail.SailReal real]
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
    (slotDisj : pins.x1 + 32 ≤ pins.sp ∨ pins.sp + 16 ≤ pins.x1) (spHi : pins.sp + 16 ≤ 2 ^ 64)
    (agreesShim : ConsumerMapAgrees spec mapping (shimMap spec mapping base pins)) :
    (∀ j, j ≤ 369 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees
      (Release.mapAt spec mapping base pins j) (stateAt real e j)) ∧
    (∀ j, 5 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧
    (stateAt real e 369).regs._PC = e.regs.gpr[30]'(by decide) ∧
    ((∀ r ∈ Residue.frameRegs, RegBind.regVal (stateAt real e 369) (.x r) = RegBind.regVal e (.x r)) ∧
      (stateAt real e 369).regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = e.regs.gpr[19]'(by decide) ∧
      (stateAt real e 369).regs.gpr[30]'(by decide) = e.regs.gpr[30]'(by decide) ∧
      (stateAt real e 369).regs.SP_EL0 = e.regs.SP_EL0 ∧
      (stateAt real e 369).regs._Z = e.regs._Z ∧
      (∀ a, ¬ Residue.StoreBytes pins mapping a → (stateAt real e 364).mem[a]? = (stateAt real e 7).mem[a]?) ∧
      (∀ i : Fin 18, RegBind.regVal (stateAt real e 364) (.x (Fin.castLE (by decide) i)) = 0#64) ∧
      (stateAt real e 364).regs.PSTATE.Z = 1#1 ∧ Release.ResidueNCV real e) ∧
    Release.Functional mapping pins e (stateAt real e 369) := by
  have allE17 := e17 real spec config rows mapping pins scope image loadBase base offS budget
    catalogue e room aligned offPre offPost codeSlot inv0 entryRows shimStatic himage hload
    mrsEntry isbEntry residue slotE spE static spAligned E codeStore slotStore low target agreesShim
  obtain ⟨dit, _, restored⟩ := dit_window real spec config rows mapping pins scope image loadBase base offS budget
    catalogue e room aligned offPre offPost codeSlot inv0 entryRows shimStatic himage hload
    mrsEntry isbEntry residue slotE spE static spAligned E codeStore slotStore low target
  obtain ⟨_, _, _, pc, _, _, _⟩ := run real spec config rows mapping pins scope image loadBase base offS budget
    catalogue e room aligned offPre offPost codeSlot inv0 entryRows shimStatic himage hload
    mrsEntry isbEntry residue slotE spE static spAligned E codeStore slotStore low target
  have abi := frame real spec config rows mapping pins scope image loadBase base offS budget
    catalogue e room aligned offPre offPost codeSlot inv0 entryRows shimStatic himage hload
    mrsEntry isbEntry residue slotE spE static spAligned E codeStore slotStore low target
  have value := functionalP real spec config rows mapping pins scope image loadBase base offS budget
    catalogue e room aligned offPre offPost codeSlot inv0 entryRows shimStatic himage hload
    mrsEntry isbEntry residue slotE spE static spAligned E codeStore slotStore low target ndPA ndSlot hd slotDisj spHi
  exact ⟨allE17, dit, restored, pc, abi, value⟩

#print axioms normalP
end ReleaseProfile.DefaultHeapShimFactory
