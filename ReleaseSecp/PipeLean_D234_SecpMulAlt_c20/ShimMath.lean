import PipeLean_D234_SecpMulAlt_c20.Shim32Exact
import PipeLean_D234_SecpMulAlt_c20.DefaultMathAgreement
import SecpInputTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts NativeMteTagCheck ReleaseProfile ArmCertValue ArmCertPipe
open CertiFFI.Prog.Generic.ModelRunView DitShim243
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts.RegBind
open CertiFFI.Prog.Generic.ModelRunView SecpMath XlateMath236.PhysicalOutput
open PipeLean_D234_SecpMulAlt_c20.DefaultMath
open ReleaseProfile.SecpInputTransport
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 4096
namespace PipeLean_D234_SecpMulAlt_c20.ShimMath

abbrev check := Shim32Exact.check

theorem run
    (real : Type)
[Sail.SailReal real]
(raw : CheckedTopology.Raw)
(config : AttributeConfig)
(rows : List PermissionRow)
(mapping : BitVec 64 → Option Nat)
(base : BitVec 64)
(pins : HeapV2E17.Pins)
(entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
(checked : check raw config rows mapping base pins entry catalogue = true) :
    (type_of% (Shim32Exact.run real raw config rows mapping base pins entry catalogue checked)) ∧
    (∃ out : LimbWords,
        physicalBytes (view EntryBinding.plan mapping entry) (stateAt real entry 112) O = (limbBytes out).map some ∧
        out.value < modulus ∧
        let inputs := Default.inputs mapping entry
        out.value = ((SubSSA.inputLimbs inputs 32).value*(SubSSA.inputLimbs inputs 32).value)%modulus) := by
  have whole := Shim32Exact.run real raw config rows mapping base pins entry catalogue checked
  have detail := whole
  obtain ⟨_,_,_,_,_,_,_,_,_,_,epimemory,prefixGPR,_⟩ := detail
  obtain ⟨topology,receipt,bodySteps,agreement,inputBytes⟩ :=
    Shim32Exact.same_state_call real raw config rows mapping base pins entry catalogue checked
  have subset : EntryBinding.plan.regions.all
      (fun pair => decide (pair ∈ EntryBinding.plan.buffers)) = true := by decide
  have bytes : ∀ r n, (r,n) ∈ EntryBinding.plan.regions → ∀ i < n,
      Physical.regionByte (view EntryBinding.plan mapping (stateAt real entry 7))
        (stateAt real entry 7) r i =
      Physical.regionByte (view EntryBinding.plan mapping entry) entry r i := by
    intro r n member i bound
    exact inputBytes r n (of_decide_eq_true (List.all_eq_true.mp subset (r,n) member)) i bound
  have inputPrefix : ∀ i < totalL EntryBinding.plan.regions,
      (Default.inputs mapping (stateAt real entry 7)).getD i 0 =
      (Default.inputs mapping entry).getD i 0 := by
    intro i inside
    exact inputs_prefix EntryBinding.plan.regions
      (view EntryBinding.plan mapping (stateAt real entry 7))
      (view EntryBinding.plan mapping entry) (stateAt real entry 7) entry bytes i inside
  have limbs_32 := input_limbs (start := 32) inputPrefix (by decide)
  obtain ⟨out,output,reduced,arithmetic⟩ := DefaultMathAgreement.arithmetic_of_agrees mapping
    (stateAt real entry 7) (stateAt real entry 108) agreement
    
  have normalized : EntryBinding.plan.normalize O = O := by decide
  have keep0 : entryGPR (stateAt real entry 7) 0 = entryGPR entry 0 := by
    simpa only [entryGPR,dite_eq_left (show 0 < 31 by decide)] using
      prefixGPR ⟨0,by decide⟩ (by decide) (by decide)
  have outputView : ∀ i < 32,
      view EntryBinding.plan mapping entry O i =
        view EntryBinding.plan mapping (stateAt real entry 7) O i := by
    intro i inside
    change mapping (BitVec.addInt (entryGPR entry 0) (0 + (i : Int))) =
      mapping (BitVec.addInt (entryGPR (stateAt real entry 7) 0) (0 + (i : Int)))
    rw [keep0]
  refine ⟨whole,out,?_,reduced,?_⟩
  · exact (output_bytes (view EntryBinding.plan mapping entry)
      (view EntryBinding.plan mapping (stateAt real entry 7))
      (stateAt real entry 112) (stateAt real entry 108) O outputView epimemory).trans output
  · simpa only [limbs_32] using arithmetic

#print axioms run
end PipeLean_D234_SecpMulAlt_c20.ShimMath
