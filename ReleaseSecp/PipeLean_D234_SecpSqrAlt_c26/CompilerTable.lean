-- GENERATED actual compiler aliases for leaf routines; no SSA mirror.
import PipeLean_D234_SecpSqrAlt_c26.Plan
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSqrAlt_c26
open ArmCertValue HeapV2StepCerts.RegBind
def D_table_c00 (tp : BitVec 64) : List Def := D_c00 tp
theorem D_table_compiles_c00 (tp : BitVec 64) : (compiled_c00 tp).map (·.1) = some (D_table_c00 tp) := rfl
theorem D_table_eq_c00 (tp : BitVec 64) : D_c00 tp = D_table_c00 tp := by
  have h := D_table_compiles_c00 tp
  rw [compiles_D_c00 tp] at h
  exact Option.some.inj h
def lrTableId_c00 : Nat := totalL rs_c00 + 30
theorem lr_table_c00 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c00 σ0_c00 n0_c00 ((plan_c00 tp).take 78)).map (fun q => q.2.regs (.x 30)) = some (some lrTableId_c00) := rfl
#print axioms D_table_eq_c00
#print axioms lr_table_c00
end PipeLean_D234_SecpSqrAlt_c26
