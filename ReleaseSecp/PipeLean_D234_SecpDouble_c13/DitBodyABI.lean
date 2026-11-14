import PipeLean_D234_SecpDouble_c13.DitBodyRun
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts.RegBind
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpDouble_c13.DitBodyABI

def preservedRegisters : List Reg := [.x 18, .x 19, .x 20, .x 21, .x 22, .x 23, .x 24, .x 25, .x 26, .x 27, .x 28, .x 29, .x 30, .sp]

def registerIndex : Reg → Nat
  | .x r => r.val
  | .sp => 31

theorem tables (tp : BitVec 64) : preservedRegisters.all (fun r =>
    decide ((finalSym_c00 tp).regs r = some (totalL rs_c00 + registerIndex r))) = true := rfl

private theorem input_register (mapping : BitVec 64 → Option Nat) (initial : NativeState) (r : Reg) :
    (Default.inputs mapping initial).getD (totalL rs_c00 + registerIndex r) 0 = regVal initial r := by
  cases r with
  | x r =>
    change (SecpCurrentEntry.inputs EntryBinding.plan mapping initial).getD
      (totalL EntryBinding.plan.regions + r.val) 0 = regVal initial (.x r)
    have value := SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial r.val r.isLt
    simpa only [entryGPR, dite_eq_left r.isLt, regVal] using value
  | sp =>
    change (SecpCurrentEntry.inputs EntryBinding.plan mapping initial).getD
      (totalL EntryBinding.plan.regions + 31) 0 = regVal initial .sp
    unfold SecpCurrentEntry.inputs
    rw [mkInputsL, mkInputsG_getD _ _ _ _ (by omega)]
    simp [inputValG, show ¬ totalL EntryBinding.plan.regions + 31 < totalL EntryBinding.plan.regions from by omega]

theorem preserved_of_agrees (mapping : BitVec 64 → Option Nat) (initial fin : NativeState)
    (agreement : ValuePlan.AgreesAt .g (view EntryBinding.plan mapping initial)
      regions_c00 σ0_c00 (Default.inputs mapping initial)
      (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 22 fin) :
    ∀ r ∈ preservedRegisters, regVal fin r = regVal initial r := by
  intro r member
  let tp := initial.regs.bank_BitVec_64 .TPIDR_EL0
  have compiled : G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    change G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp)
    rw [Default.inputs_length]; exact compiles_D_c00 tp
  have symbolic := of_decide_eq_true (List.all_eq_true.mp (tables tp) r member)
  have taken : (plan_c00 tp).take 22 = plan_c00 tp := by
    apply List.take_of_length_le
    rw [plan_length_c00]
    omega
  have current : (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length
      ((plan_c00 tp).take 22)).map (fun q => q.2.regs r) =
        some (some (totalL rs_c00 + registerIndex r)) := by
    rw [taken, compiled]
    simpa only [Option.map_some] using congrArg some symbolic
  have value := ValuePlan.register_value .g (view EntryBinding.plan mapping initial)
    regions_c00 σ0_c00 (Default.inputs mapping initial) (plan_c00 tp) 22 fin
    (D_c00 tp) (finalSym_c00 tp) agreement compiled r (totalL rs_c00 + registerIndex r) current
  have indexBound : totalL rs_c00 + registerIndex r < (Default.inputs mapping initial).length := by
    rw [Default.inputs_length]
    change totalL rs_c00 + registerIndex r < totalL rs_c00 + 36
    cases r <;> simp only [registerIndex] <;> omega
  rw [getD_extend_input _ _ indexBound] at value
  exact value.trans (input_register mapping initial r)

theorem run (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    (∀ k, k < 22 → modelStep real (stateAt real initial k) = .ok () (stateAt real initial (k+1))) ∧
    ∃ fin, fin = stateAt real initial 22 ∧
      (∀ r ∈ preservedRegisters, regVal fin r = regVal initial r) ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) initial fin ∧
      fin.regs._PC = entryGPR initial 30 ∧
      ∃ used, NativeMteTagCheck.ChoiceDelta initial fin used ∧ used ≤ DefaultState.capacity initial := by
  obtain ⟨topology,steps,invariants,fin,last,finEq,agreement,frame,returned,used,delta,bound⟩ :=
    DitBodyRun.run real raw config rows mapping base initial topology receipt
  exact ⟨steps,fin,finEq,preserved_of_agrees mapping initial fin agreement,frame,returned,used,delta,bound⟩

#print axioms tables
#print axioms run
end PipeLean_D234_SecpDouble_c13.DitBodyABI
