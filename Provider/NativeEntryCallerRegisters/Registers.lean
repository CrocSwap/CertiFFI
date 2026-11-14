import NativeEntryCallerParts.BlCall
import NativeEntryCallerParts.BlrCall
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryCallerRegisters
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def linkValue (s : NativeState) : BitVec 64 :=
  Sail.BitVec.zeroExtend (Sail.BitVec.addInt s.regs._PC (4 : Int)) 64

theorem link_value (s : NativeState) : linkValue s = s.regs._PC + 4#64 := by
  simp [linkValue, Sail.BitVec.zeroExtend, Sail.BitVec.addInt]

theorem bl_gpr (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.gpr = s.regs.gpr.set 30 (linkValue s) := by
  unfold blActionState
  rw [branch_gpr]
  rfl

theorem bl_lr (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.gpr[30] = s.regs._PC + 4#64 := by
  rw [bl_gpr]
  simpa using link_value s

theorem bl_other (imm26 : BitVec 26) (s : NativeState) (r : Fin 31)
    (other : r.val ≠ 30) :
    (blActionState imm26 s).regs.gpr[r.val] = s.regs.gpr[r.val] := by
  rw [bl_gpr]
  simp [Ne.symm other]

theorem blr_gpr (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.gpr = s.regs.gpr.set 30 (linkValue s) := by
  unfold blrActionState
  rw [branch_gpr]
  rfl

theorem blr_lr (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.gpr[30] = s.regs._PC + 4#64 := by
  rw [blr_gpr]
  simpa using link_value s

theorem blr_other (Rn : BitVec 5) (s : NativeState) (r : Fin 31)
    (other : r.val ≠ 30) :
    (blrActionState Rn s).regs.gpr[r.val] = s.regs.gpr[r.val] := by
  rw [blr_gpr]
  simp [Ne.symm other]

theorem bl_target (imm26 : BitVec 26) (s : NativeState) :
    blTarget imm26 s = s.regs._PC + sign_extend (imm26 ++ (0#2)) 64 := rfl

theorem blr_target_key (Rn : BitVec 5) (s : NativeState) :
    blrTarget Rn s = s.regs.gpr[(GPRSummary.key Rn.toNat).val] := by
  unfold blrTarget
  change Sail.BitVec.extractLsb (s.regs.gpr[(GPRSummary.key Rn.toNat).val]) 63 0 = _
  exact full_extract _

theorem key_rn : ∀ Rn : BitVec 5, Rn.toNat < 31 →
    (GPRSummary.key Rn.toNat).val = Rn.toNat := by decide +kernel

theorem blr_target (Rn : BitVec 5) (s : NativeState) (rn : Rn.toNat < 31) :
    blrTarget Rn s = s.regs.gpr[Rn.toNat] := by
  rw [blr_target_key]
  simp only [key_rn Rn rn]

#print axioms link_value
#print axioms bl_gpr
#print axioms bl_lr
#print axioms bl_other
#print axioms blr_gpr
#print axioms blr_lr
#print axioms blr_other
#print axioms bl_target
#print axioms blr_target_key
#print axioms key_rn
#print axioms blr_target
end NativeEntryCallerRegisters
