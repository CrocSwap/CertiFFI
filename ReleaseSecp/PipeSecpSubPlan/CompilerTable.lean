-- GENERATED actual compiler aliases for leaf routines; no SSA mirror.
import PipeSecpSubPlan.Plan
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeSecpSubPlan
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
end PipeSecpSubPlan
