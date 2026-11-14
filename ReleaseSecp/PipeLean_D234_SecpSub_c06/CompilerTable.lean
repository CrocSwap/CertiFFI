-- GENERATED actual compiler aliases for leaf routines; no SSA mirror.
import PipeLean_D234_SecpSub_c06.Plan
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c06
open ArmCertValue HeapV2StepCerts.RegBind
def D_table_c06 (tp : BitVec 64) : List Def := D_c06 tp
theorem D_table_compiles_c06 (tp : BitVec 64) : (compiled_c06 tp).map (·.1) = some (D_table_c06 tp) := rfl
theorem D_table_eq_c06 (tp : BitVec 64) : D_c06 tp = D_table_c06 tp := by
  have h := D_table_compiles_c06 tp
  rw [compiles_D_c06 tp] at h
  exact Option.some.inj h
def lrTableId_c06 : Nat := totalL rs_c06 + 30
theorem lr_table_c06 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06 ((plan_c06 tp).take 17)).map (fun q => q.2.regs (.x 30)) = some (some lrTableId_c06) := rfl
#print axioms D_table_eq_c06
#print axioms lr_table_c06
end PipeLean_D234_SecpSub_c06
