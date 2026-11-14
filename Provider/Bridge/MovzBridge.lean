import Bridge.MovzPins
import Bridge.Proj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.Boundary
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.MovzBridgeLNSym.
namespace ArmBridge.Movz

theorem bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  rcases x with ⟨⟨v, hv⟩⟩
  rcases (by omega : v = 0 ∨ v = 1) with h | h <;> subst h <;> simp

theorem bv2_cases (x : BitVec 2) : x = 0#2 ∨ x = 1#2 ∨ x = 2#2 ∨ x = 3#2 := by
  rcases x with ⟨⟨v, hv⟩⟩
  rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3) with h | h | h | h <;> subst h <;> simp

theorem w64a : Sail.Int.toNatChecked (if (1#1 : BitVec 1) = 1#1 then (64 : Int) else 32) = 64 := rfl

theorem w32a : Sail.Int.toNatChecked (if (0#1 : BitVec 1) = 1#1 then (64 : Int) else 32) = 32 := rfl

theorem w64 : Sail.Int.toNatChecked (64 : Int) = 64 := rfl

theorem w32 : Sail.Int.toNatChecked (32 : Int) = 32 := rfl

theorem d64 : (32 <<< (1#1 : BitVec 1).toNat) = 64 := rfl

theorem d32 : (32 <<< (0#1 : BitVec 1).toNat) = 32 := rfl

theorem rd_PSTATE (s : NativeState) : (readReg PSTATE : SailM ProcState) s = .ok s.regs.PSTATE s := rfl

theorem rd_BTypeNext (s : NativeState) : (readReg BTypeNext : SailM (BitVec 2)) s = .ok s.regs.BTypeNext s := rfl

theorem rd_BranchTaken (s : NativeState) : (readReg __BranchTaken : SailM Bool) s = .ok s.regs.__BranchTaken s := rfl

theorem rd_PC (s : NativeState) : (readReg _PC : SailM (BitVec 64)) s = .ok s.regs._PC s := rfl

theorem wr_PSTATE (s : NativeState) (v : ProcState) :
    (writeReg PSTATE v : SailM Unit) s = .ok () { s with regs := { s.regs with PSTATE := v } } := rfl

theorem wr_PC (s : NativeState) (v : BitVec 64) :
    (writeReg _PC v : SailM Unit) s = .ok () { s with regs := { s.regs with _PC := v } } := rfl

/-- Legal MOVN/MOVZ/MOVK encodings (the model and LNSym both reject the others). -/
def Legal (sf : BitVec 1) (opc : BitVec 2) (hw : BitVec 2) : Prop :=
  opc ≠ 1#2 ∧ ¬ (sf = 0#1 ∧ hw.getLsbD 1 = true)

end ArmBridge.Movz

