import M1a.PathWalk
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a
open S1OuterSetup ArmCert.Eval.JointSAT S1LogicalReference

/- J3c (item 2,): J3b plus one CODE page for the IFETCH instance.
   VA 0x1000 -> PA 0x606000000 via L3 entry B4+8. Realistic user-code leaf (ee = 0 is
   proved for the EL20 Get, so no palindrome): AP = 11 (RO), AF = 1, nG = 1, SH inner,
   AttrIndx 0, PXN = 1, UXN = 0, DBM = 0, contiguous = 0, GP = 0. -/
def codeLeaf : BitVec 64 := 0x0020000606000fc3#64

open J3b in
def loadC (m : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  put (load m) (B4 + 8) codeLeaf

open J3b in
theorem loadC_mem (m : Std.ExtHashMap Nat (BitVec 8)) : ∀ a d, ((a = B1 ∧ d = d1) ∨
    (a = B2 ∧ d = d2) ∨ (a = B3 ∧ d = d3) ∨ (a = B4 + 8 ∧ d = codeLeaf)) → ∀ i, i < 8 →
    (loadC m)[a + i]? = some (byte false d i) := by
  intro a d hs i hi
  unfold loadC
  rcases hs with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
  · rw [put_other _ _ _ _ (by unfold B4 B1; omega)]
    exact load_get m _ _ (Or.inl ⟨rfl, rfl⟩) i hi
  · rw [put_other _ _ _ _ (by unfold B4 B2; omega)]
    exact load_get m _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩)) i hi
  · rw [put_other _ _ _ _ (by unfold B4 B3; omega)]
    exact load_get m _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) i hi
  · exact put_same _ _ _ _ hi

/-- Loader step (EL2&0): J3c bytes plus TTBR0_EL2/HTTBR = B1. -/
def prep20c (s : State) : State :=
  {s with mem := loadC s.mem,
          regs := (Regs.ref_BitVec_128 ._TTBR0_EL2).set (BitVec.ofNat 128 J3b.B1)
            ((Regs.ref_BitVec_64 .HTTBR).set (BitVec.ofNat 64 J3b.B1) s.regs)}

theorem prep20c_facts (s : State) :
    (prep20c s).regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled ∧
    (prep20c s).mem = loadC s.mem ∧
    (prep20c s).regs.bank_BitVec_128 ._TTBR0_EL2 = BitVec.ofNat 128 J3b.B1 ∧
    (prep20c s).regs.bank_BitVec_64 .HTTBR = BitVec.ofNat 64 J3b.B1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [prep20c, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]
  · dsimp only [prep20c]
  · simp [prep20c, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]
  · simp [prep20c, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]



end ArmCert.Eval.M1a
