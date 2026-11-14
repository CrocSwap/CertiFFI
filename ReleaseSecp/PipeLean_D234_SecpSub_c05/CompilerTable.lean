-- GENERATED actual compiler aliases for leaf routines; no SSA mirror.
import PipeLean_D234_SecpSub_c05.Plan
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c05
open ArmCertValue HeapV2StepCerts.RegBind
def D_table_c05 (tp : BitVec 64) : List Def := D_c05 tp
theorem D_table_compiles_c05 (tp : BitVec 64) : (compiled_c05 tp).map (·.1) = some (D_table_c05 tp) := rfl
theorem D_table_eq_c05 (tp : BitVec 64) : D_c05 tp = D_table_c05 tp := by
  have h := D_table_compiles_c05 tp
  rw [compiles_D_c05 tp] at h
  exact Option.some.inj h
def lrTableId_c05 : Nat := totalL rs_c05 + 30
theorem lr_table_c05 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c05 σ0_c05 n0_c05 ((plan_c05 tp).take 17)).map (fun q => q.2.regs (.x 30)) = some (some lrTableId_c05) := rfl
#print axioms D_table_eq_c05
#print axioms lr_table_c05
end PipeLean_D234_SecpSub_c05
