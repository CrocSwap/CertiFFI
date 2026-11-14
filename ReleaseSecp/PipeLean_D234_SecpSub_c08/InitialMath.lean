import PipeLean_D234_SecpSub_c08.Shim32Exact
import SecpMath.SubSSA
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
namespace PipeLean_D234_SecpSub_c08.InitialMath

theorem arithmetic_rows (tp : BitVec 64) : SubSSA.RowPositions (D_c08 tp) n0_c08 := by
  constructor <;> rfl

theorem load_rows (tp : BitVec 64) : SubSSA.LoadPositions (D_c08 tp) 32 0 := by
  constructor <;> rfl

def outputIds : List (Nat × Nat) := [(n0_c08+31,0), (n0_c08+31,1), (n0_c08+31,2), (n0_c08+31,3), (n0_c08+31,4), (n0_c08+31,5), (n0_c08+31,6), (n0_c08+31,7), (n0_c08+36,0), (n0_c08+36,1), (n0_c08+36,2), (n0_c08+36,3), (n0_c08+36,4), (n0_c08+36,5), (n0_c08+36,6), (n0_c08+36,7), (n0_c08+41,0), (n0_c08+41,1), (n0_c08+41,2), (n0_c08+41,3), (n0_c08+41,4), (n0_c08+41,5), (n0_c08+41,6), (n0_c08+41,7), (n0_c08+46,0), (n0_c08+46,1), (n0_c08+46,2), (n0_c08+46,3), (n0_c08+46,4), (n0_c08+46,5), (n0_c08+46,6), (n0_c08+46,7)]

theorem output_ids (tp : BitVec 64) :
    (List.range 32).map ((finalSym_c08 tp).memB O) = outputIds.map some := rfl

private theorem output_bytes (values : List (BitVec 64)) (tp : BitVec 64)
    (mapping : Physical.BytePA) (fin : NativeState)
    (agrees : Physical.Agrees mapping values (finalSym_c08 tp) fin) :
    physicalBytes mapping fin O =
      (limbBytes (SubSSA.resultWords (fun i => values.getD i 0) n0_c08)).map some := by
  rw [physical_bytes_of_agrees values (finalSym_c08 tp) O mapping fin outputIds agrees (output_ids tp)]
  rw [bytes_of_ids values (finalSym_c08 tp) O outputIds (output_ids tp)]
  rfl

theorem arithmetic_of_agrees
    (mapping : BitVec 64 → Option Nat) (initial fin : NativeState)
    (agreement : ValuePlan.AgreesAt .f (view EntryBinding.plan mapping initial)
      regions_c08 σ0_c08 (Default.inputs mapping initial)
      (plan_c08 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 18 fin)
    (hx : (SubSSA.inputLimbs (Default.inputs mapping initial) 32).value < modulus)
    (hy : (SubSSA.inputLimbs (Default.inputs mapping initial) 0).value < modulus) :
    ∃ out : LimbWords,
        physicalBytes (view EntryBinding.plan mapping initial) fin O = (limbBytes out).map some ∧
        out.value < modulus ∧
        let inputs := Default.inputs mapping initial
        (out.value : Int) = (((SubSSA.inputLimbs inputs 32).value : Int)-((SubSSA.inputLimbs inputs 0).value : Int))%(modulus : Int) := by
  let tp := initial.regs.bank_BitVec_64 .TPIDR_EL0
  let inputs := Default.inputs mapping initial
  have compiled : F.compileRun regions_c08 σ0_c08 inputs.length (plan_c08 tp) =
      some (D_c08 tp,finalSym_c08 tp) := by
    change F.compileRun regions_c08 σ0_c08 (Default.inputs mapping initial).length (plan_c08 tp) = _
    rw [Default.inputs_length]; exact compiles_D_c08 tp
  change ArmCertPipe.F.AgreesAt (view EntryBinding.plan mapping initial) regions_c08 σ0_c08
    inputs (plan_c08 tp) 18 fin at agreement
  obtain ⟨defs,sym,prefixCompiled,physical,bounded⟩ := agreement
  have taken : (plan_c08 tp).take 18 = plan_c08 tp := by
    apply List.take_of_length_le
    rw [plan_length_c08]
    omega
  rw [taken] at prefixCompiled
  have same : (defs,sym) = (D_c08 tp,finalSym_c08 tp) := Option.some.inj (prefixCompiled.symm.trans compiled)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  have length : inputs.length = n0_c08 := Default.inputs_length mapping initial
  have arithmetic := SubSSA.table_correct inputs (D_c08 tp) n0_c08 32 0 length
    (arithmetic_rows tp) (load_rows tp) (by decide) (by decide) hx hy
  refine ⟨SubSSA.resultWords (fun i => (extend inputs (D_c08 tp)).getD i 0) n0_c08,?_,?_⟩
  · exact output_bytes _ tp _ fin physical
  · simpa only [evalDefs] using arithmetic

#print axioms arithmetic_rows
#print axioms load_rows
#print axioms output_ids
#print axioms arithmetic_of_agrees
end PipeLean_D234_SecpSub_c08.InitialMath
