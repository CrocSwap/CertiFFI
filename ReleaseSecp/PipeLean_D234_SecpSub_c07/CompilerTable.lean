-- GENERATED actual compiler aliases for leaf routines; no SSA mirror.
import PipeLean_D234_SecpSub_c07.Plan
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c07
open ArmCertValue HeapV2StepCerts.RegBind
def D_table_c07 (tp : BitVec 64) : List Def := D_c07 tp
theorem D_table_compiles_c07 (tp : BitVec 64) : (compiled_c07 tp).map (·.1) = some (D_table_c07 tp) := rfl
theorem D_table_eq_c07 (tp : BitVec 64) : D_c07 tp = D_table_c07 tp := by
  have h := D_table_compiles_c07 tp
  rw [compiles_D_c07 tp] at h
  exact Option.some.inj h
def lrTableId_c07 : Nat := totalL rs_c07 + 30
theorem lr_table_c07 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c07 σ0_c07 n0_c07 ((plan_c07 tp).take 17)).map (fun q => q.2.regs (.x 30)) = some (some lrTableId_c07) := rfl
#print axioms D_table_eq_c07
#print axioms lr_table_c07
end PipeLean_D234_SecpSub_c07
