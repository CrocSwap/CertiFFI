-- GENERATED actual compiler aliases for leaf routines; no SSA mirror.
import PipeLean_D234_SecpSub_c08.Plan
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c08
open ArmCertValue HeapV2StepCerts.RegBind
def D_table_c08 (tp : BitVec 64) : List Def := D_c08 tp
theorem D_table_compiles_c08 (tp : BitVec 64) : (compiled_c08 tp).map (·.1) = some (D_table_c08 tp) := rfl
theorem D_table_eq_c08 (tp : BitVec 64) : D_c08 tp = D_table_c08 tp := by
  have h := D_table_compiles_c08 tp
  rw [compiles_D_c08 tp] at h
  exact Option.some.inj h
def lrTableId_c08 : Nat := totalL rs_c08 + 30
theorem lr_table_c08 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c08 σ0_c08 n0_c08 ((plan_c08 tp).take 17)).map (fun q => q.2.regs (.x 30)) = some (some lrTableId_c08) := rfl
#print axioms D_table_eq_c08
#print axioms lr_table_c08
end PipeLean_D234_SecpSub_c08
