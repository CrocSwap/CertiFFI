import PipeLean_D234_SecpSqrAlt_c27.DefaultRun
import SecpMath.SqrAltSSA
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
namespace PipeLean_D234_SecpSqrAlt_c27.DefaultMath

private theorem compiler_rows (tp : BitVec 64) :
    D_c00 tp = SqrAltSSA.compilerRows n0_c00 0 := rfl

theorem arithmetic_rows (tp : BitVec 64) : SqrAltSSA.RowPositions (D_c00 tp) n0_c00 := by
  rw [compiler_rows tp]
  exact SqrAltSSA.row_positions _ _

theorem load_rows (tp : BitVec 64) : SqrAltSSA.LoadPositions (D_c00 tp) 0 := by
  rw [compiler_rows tp]
  exact SqrAltSSA.load_positions _ _

def outputIds : List (Nat × Nat) := [(n0_c00+190,0), (n0_c00+190,1), (n0_c00+190,2), (n0_c00+190,3), (n0_c00+190,4), (n0_c00+190,5), (n0_c00+190,6), (n0_c00+190,7), (n0_c00+195,0), (n0_c00+195,1), (n0_c00+195,2), (n0_c00+195,3), (n0_c00+195,4), (n0_c00+195,5), (n0_c00+195,6), (n0_c00+195,7), (n0_c00+200,0), (n0_c00+200,1), (n0_c00+200,2), (n0_c00+200,3), (n0_c00+200,4), (n0_c00+200,5), (n0_c00+200,6), (n0_c00+200,7), (n0_c00+205,0), (n0_c00+205,1), (n0_c00+205,2), (n0_c00+205,3), (n0_c00+205,4), (n0_c00+205,5), (n0_c00+205,6), (n0_c00+205,7)]

theorem output_ids (tp : BitVec 64) :
    (List.range 32).map ((finalSym_c00 tp).memB O) = outputIds.map some := rfl

private theorem output_bytes (values : List (BitVec 64)) (tp : BitVec 64)
    (mapping : Physical.BytePA) (fin : NativeState)
    (agrees : Physical.Agrees mapping values (finalSym_c00 tp) fin) :
    physicalBytes mapping fin O =
      (limbBytes (SqrAltSSA.resultWords (fun i => values.getD i 0) n0_c00)).map some := by
  rw [physical_bytes_of_agrees values (finalSym_c00 tp) O mapping fin outputIds agrees (output_ids tp)]
  rw [bytes_of_ids values (finalSym_c00 tp) O outputIds (output_ids tp)]
  rfl

theorem run (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true) :
    (∀ k, k < 79 → modelStep real (stateAt real initial k) = .ok () (stateAt real initial (k+1))) ∧
    ∃ fin, fin = stateAt real initial 79 ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) initial fin ∧
      fin.regs._PC = entryGPR initial 30 ∧
      ∃ out : LimbWords,
        physicalBytes (view EntryBinding.plan mapping initial) fin O = (limbBytes out).map some ∧
        out.value < modulus ∧
        let inputs := Default.inputs mapping initial
        out.value = ((SubSSA.inputLimbs inputs 0).value*(SubSSA.inputLimbs inputs 0).value)%modulus := by
  obtain ⟨topology,steps,invariants,fin,last,finEq,agreement,frame,returned,trace⟩ :=
    DefaultRun.run real raw config rows mapping base initial catalogue checked
  let tp := initial.regs.bank_BitVec_64 .TPIDR_EL0
  let inputs := Default.inputs mapping initial
  have compiled : F.compileRun regions_c00 σ0_c00 inputs.length (plan_c00 tp) =
      some (D_c00 tp,finalSym_c00 tp) := by
    change F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 tp) = _
    rw [Default.inputs_length]; exact compiles_D_c00 tp
  change ArmCertPipe.F.AgreesAt (view EntryBinding.plan mapping initial) regions_c00 σ0_c00
    inputs (plan_c00 tp) 79 fin at agreement
  obtain ⟨defs,sym,prefixCompiled,physical,bounded⟩ := agreement
  have taken : (plan_c00 tp).take 79 = plan_c00 tp := by
    apply List.take_of_length_le
    rw [plan_length_c00]
    omega
  rw [taken] at prefixCompiled
  have same : (defs,sym) = (D_c00 tp,finalSym_c00 tp) := Option.some.inj (prefixCompiled.symm.trans compiled)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  have length : inputs.length = n0_c00 := Default.inputs_length mapping initial
  have arithmetic := SqrAltSSA.table_correct inputs (D_c00 tp) n0_c00 0 length
    (arithmetic_rows tp) (load_rows tp) (by decide)
  refine ⟨steps,fin,finEq,frame,returned,SqrAltSSA.resultWords (fun i => (extend inputs (D_c00 tp)).getD i 0) n0_c00,?_,?_⟩
  · exact output_bytes _ tp _ fin physical
  · simpa only [evalDefs] using arithmetic

#print axioms arithmetic_rows
#print axioms load_rows
#print axioms output_ids
#print axioms run
end PipeLean_D234_SecpSqrAlt_c27.DefaultMath
