import PipeLean_D234_SecpMul_c15.DefaultMath
import SecpMath.MainMulSSA
import XlateMath236.PhysicalOutput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts.RegBind
open CertiFFI.Prog.Generic.ModelRunView SecpMath XlateMath236.PhysicalOutput
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
open PipeLean_D234_SecpMul_c15.DefaultMath
namespace PipeLean_D234_SecpMul_c15.DefaultMathAgreement

private theorem output_bytes (values : List (BitVec 64)) (tp : BitVec 64)
    (mapping : Physical.BytePA) (fin : NativeState)
    (agrees : Physical.Agrees mapping values (finalSym_c00 tp) fin) :
    physicalBytes mapping fin O =
      (limbBytes (MainMulSSA.resultWords (fun i => values.getD i 0) n0_c00)).map some := by
  rw [physical_bytes_of_agrees values (finalSym_c00 tp) O mapping fin outputIds agrees (output_ids tp)]
  rw [bytes_of_ids values (finalSym_c00 tp) O outputIds (output_ids tp)]
  rfl

theorem arithmetic_of_agrees
    (mapping : BitVec 64 → Option Nat) (initial fin : NativeState)
    (agreement : ValuePlan.AgreesAt .g (view EntryBinding.plan mapping initial)
      regions_c00 σ0_c00 (Default.inputs mapping initial)
      (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 158 fin)
    : ∃ out : LimbWords,
        physicalBytes (view EntryBinding.plan mapping initial) fin O = (limbBytes out).map some ∧
        out.value < modulus ∧
        let inputs := Default.inputs mapping initial
        out.value = ((SubSSA.inputLimbs inputs 32).value*(SubSSA.inputLimbs inputs 32).value)%modulus := by
  let tp := initial.regs.bank_BitVec_64 .TPIDR_EL0
  let inputs := Default.inputs mapping initial
  have compiled : G.compileRun regions_c00 σ0_c00 inputs.length (plan_c00 tp) =
      some (D_c00 tp,finalSym_c00 tp) := by
    change G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 tp) = _
    rw [Default.inputs_length]; exact compiles_D_c00 tp
  change ArmCertPipe.G.AgreesAt (view EntryBinding.plan mapping initial) regions_c00 σ0_c00
    inputs (plan_c00 tp) 158 fin at agreement
  obtain ⟨defs,sym,prefixCompiled,physical,bounded⟩ := agreement
  have taken : (plan_c00 tp).take 158 = plan_c00 tp := by
    apply List.take_of_length_le
    rw [plan_length_c00]
    omega
  rw [taken] at prefixCompiled
  have same : (defs,sym) = (D_c00 tp,finalSym_c00 tp) := Option.some.inj (prefixCompiled.symm.trans compiled)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  have length : inputs.length = n0_c00 := Default.inputs_length mapping initial
  have arithmetic := MainMulSSA.table_correct inputs (D_c00 tp) n0_c00 32 32 length
    (arithmetic_rows tp) (load_rows tp) (by decide) (by decide)
  refine ⟨MainMulSSA.resultWords (fun i => (extend inputs (D_c00 tp)).getD i 0) n0_c00,?_,?_⟩
  · exact output_bytes _ tp _ fin physical
  · simpa only [evalDefs] using arithmetic


#print axioms arithmetic_of_agrees
end PipeLean_D234_SecpMul_c15.DefaultMathAgreement
