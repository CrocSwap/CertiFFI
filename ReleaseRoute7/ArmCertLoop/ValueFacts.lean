import LoopNative.Arithmetic
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft
open ArmCertValue HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.ValueFacts

theorem single_gpr (written : Fin 31) (value : VUpd) (flags : Option (VUpd × VUpd × VUpd × VUpd))
    (before after : NativeState) (holds : VHolds [(.x written, some value)] flags before after) :
    after.regs.gpr = before.regs.gpr.set written.val (value.eval before) := by
  apply Vector.ext
  intro i bounded
  have h := holds.1 (.x ⟨i, bounded⟩)
  by_cases same : written.val = i
  · have equal : written = ⟨i, bounded⟩ := Fin.ext same
    subst written
    simpa [regVal] using h
  · have different : Reg.x written ≠ Reg.x ⟨i, bounded⟩ := by
      intro equal
      cases equal
      exact same rfl
    simpa [regVal, different, Vector.getElem_set, same] using h

theorem single_sp (written : Fin 31) (value : VUpd) (flags : Option (VUpd × VUpd × VUpd × VUpd))
    (before after : NativeState) (holds : VHolds [(.x written, some value)] flags before after) :
    after.regs.SP_EL0 = before.regs.SP_EL0 := by
  have h := holds.1 .sp
  simpa [regVal] using h

theorem nil_gpr (before after : NativeState) (holds : VHolds [] none before after) :
    after.regs.gpr = before.regs.gpr := by
  apply Vector.ext
  intro i bounded
  exact holds.1 (.x ⟨i, bounded⟩)

theorem nil_sp (before after : NativeState) (holds : VHolds [] none before after) :
    after.regs.SP_EL0 = before.regs.SP_EL0 := holds.1 .sp

theorem add (Rd Rn : BitVec 5) (imm12 : BitVec 12) (before after : NativeState)
    (holds : VHolds (LoopNative.AddImm64.upd Rd Rn imm12) none before after) :
    after.regs.gpr = before.regs.gpr.set (rk Rd).val
      (before.regs.gpr[(rk Rn).val] + imm12.setWidth 64) ∧ after.regs.SP_EL0 = before.regs.SP_EL0 :=
  ⟨single_gpr (rk Rd) _ none before after holds, single_sp (rk Rd) _ none before after holds⟩

theorem sub (Rd Rn : BitVec 5) (imm12 : BitVec 12) (before after : NativeState)
    (holds : VHolds (LoopNative.SubImm64.upd Rd Rn imm12) none before after) :
    after.regs.gpr = before.regs.gpr.set (rk Rd).val
      (before.regs.gpr[(rk Rn).val] - imm12.setWidth 64) ∧ after.regs.SP_EL0 = before.regs.SP_EL0 :=
  ⟨single_gpr (rk Rd) _ none before after holds, single_sp (rk Rd) _ none before after holds⟩

theorem mov (Rd Rm : BitVec 5) (before after : NativeState)
    (holds : VHolds (LoopNative.Mov64.upd Rd Rm) none before after) :
    after.regs.gpr = before.regs.gpr.set (rk Rd).val before.regs.gpr[(rk Rm).val] ∧
      after.regs.SP_EL0 = before.regs.SP_EL0 := by
  let value : VUpd := ⟨.add, [.reg (.x (rk Rm)), .lit 0#64]⟩
  have gpr := single_gpr (rk Rd) value none before after holds
  change after.regs.gpr = before.regs.gpr.set (rk Rd).val (before.regs.gpr[(rk Rm).val] + 0#64) at gpr
  exact ⟨by simpa only [BitVec.add_zero] using gpr, single_sp (rk Rd) value none before after holds⟩

#print axioms single_gpr
#print axioms single_sp
#print axioms nil_gpr
#print axioms nil_sp
#print axioms add
#print axioms sub
#print axioms mov
end ArmCertLoop.ValueFacts
