-- GENERATED actual compiler aliases for leaf routines; no SSA mirror.
import PipeLean_D234_SecpSub_c09.Plan
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c09
open ArmCertValue HeapV2StepCerts.RegBind
def D_table_c09 (tp : BitVec 64) : List Def := D_c09 tp
theorem D_table_compiles_c09 (tp : BitVec 64) : (compiled_c09 tp).map (·.1) = some (D_table_c09 tp) := rfl
theorem D_table_eq_c09 (tp : BitVec 64) : D_c09 tp = D_table_c09 tp := by
  have h := D_table_compiles_c09 tp
  rw [compiles_D_c09 tp] at h
  exact Option.some.inj h
def lrTableId_c09 : Nat := totalL rs_c09 + 30
theorem lr_table_c09 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c09 σ0_c09 n0_c09 ((plan_c09 tp).take 17)).map (fun q => q.2.regs (.x 30)) = some (some lrTableId_c09) := rfl
#print axioms D_table_eq_c09
#print axioms lr_table_c09
end PipeLean_D234_SecpSub_c09
