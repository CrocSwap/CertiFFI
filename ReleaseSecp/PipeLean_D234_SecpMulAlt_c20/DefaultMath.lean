import PipeLean_D234_SecpMulAlt_c20.DefaultRun
import SecpMath.MulAltSSA
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
namespace PipeLean_D234_SecpMulAlt_c20.DefaultMath

private theorem compiler_rows (tp : BitVec 64) :
    D_c00 tp = MulAltSSA.compilerRows n0_c00 32 32 := rfl

theorem arithmetic_rows (tp : BitVec 64) : MulAltSSA.RowPositions (D_c00 tp) n0_c00 := by
  rw [compiler_rows tp]
  exact MulAltSSA.row_positions _ _ _

theorem load_rows (tp : BitVec 64) : MulAltSSA.LoadPositions (D_c00 tp) 32 32 := by
  rw [compiler_rows tp]
  exact MulAltSSA.load_positions _ _ _

def outputIds : List (Nat × Nat) := [(n0_c00+238,0), (n0_c00+238,1), (n0_c00+238,2), (n0_c00+238,3), (n0_c00+238,4), (n0_c00+238,5), (n0_c00+238,6), (n0_c00+238,7), (n0_c00+243,0), (n0_c00+243,1), (n0_c00+243,2), (n0_c00+243,3), (n0_c00+243,4), (n0_c00+243,5), (n0_c00+243,6), (n0_c00+243,7), (n0_c00+248,0), (n0_c00+248,1), (n0_c00+248,2), (n0_c00+248,3), (n0_c00+248,4), (n0_c00+248,5), (n0_c00+248,6), (n0_c00+248,7), (n0_c00+253,0), (n0_c00+253,1), (n0_c00+253,2), (n0_c00+253,3), (n0_c00+253,4), (n0_c00+253,5), (n0_c00+253,6), (n0_c00+253,7)]

theorem output_ids (tp : BitVec 64) :
    (List.range 32).map ((finalSym_c00 tp).memB O) = outputIds.map some := rfl

private theorem output_bytes (values : List (BitVec 64)) (tp : BitVec 64)
    (mapping : Physical.BytePA) (fin : NativeState)
    (agrees : Physical.Agrees mapping values (finalSym_c00 tp) fin) :
    physicalBytes mapping fin O =
      (limbBytes (MulAltSSA.resultWords (fun i => values.getD i 0) n0_c00)).map some := by
  rw [physical_bytes_of_agrees values (finalSym_c00 tp) O mapping fin outputIds agrees (output_ids tp)]
  rw [bytes_of_ids values (finalSym_c00 tp) O outputIds (output_ids tp)]
  rfl

theorem run (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true) :
    (∀ k, k < 101 → modelStep real (stateAt real initial k) = .ok () (stateAt real initial (k+1))) ∧
    ∃ fin, fin = stateAt real initial 101 ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) initial fin ∧
      fin.regs._PC = entryGPR initial 30 ∧
      ∃ out : LimbWords,
        physicalBytes (view EntryBinding.plan mapping initial) fin O = (limbBytes out).map some ∧
        out.value < modulus ∧
        let inputs := Default.inputs mapping initial
        out.value = ((SubSSA.inputLimbs inputs 32).value*(SubSSA.inputLimbs inputs 32).value)%modulus := by
  obtain ⟨topology,steps,invariants,fin,last,finEq,agreement,frame,returned,trace⟩ :=
    DefaultRun.run real raw config rows mapping base initial catalogue checked
  let tp := initial.regs.bank_BitVec_64 .TPIDR_EL0
  let inputs := Default.inputs mapping initial
  have compiled : F.compileRun regions_c00 σ0_c00 inputs.length (plan_c00 tp) =
      some (D_c00 tp,finalSym_c00 tp) := by
    change F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 tp) = _
    rw [Default.inputs_length]; exact compiles_D_c00 tp
  change ArmCertPipe.F.AgreesAt (view EntryBinding.plan mapping initial) regions_c00 σ0_c00
    inputs (plan_c00 tp) 101 fin at agreement
  obtain ⟨defs,sym,prefixCompiled,physical,bounded⟩ := agreement
  have taken : (plan_c00 tp).take 101 = plan_c00 tp := by
    apply List.take_of_length_le
    rw [plan_length_c00]
    omega
  rw [taken] at prefixCompiled
  have same : (defs,sym) = (D_c00 tp,finalSym_c00 tp) := Option.some.inj (prefixCompiled.symm.trans compiled)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  have length : inputs.length = n0_c00 := Default.inputs_length mapping initial
  have arithmetic := MulAltSSA.table_correct inputs (D_c00 tp) n0_c00 32 32 length
    (arithmetic_rows tp) (load_rows tp) (by decide) (by decide)
  refine ⟨steps,fin,finEq,frame,returned,MulAltSSA.resultWords (fun i => (extend inputs (D_c00 tp)).getD i 0) n0_c00,?_,?_⟩
  · exact output_bytes _ tp _ fin physical
  · simpa only [evalDefs] using arithmetic

#print axioms arithmetic_rows
#print axioms load_rows
#print axioms output_ids
#print axioms run
end PipeLean_D234_SecpMulAlt_c20.DefaultMath
