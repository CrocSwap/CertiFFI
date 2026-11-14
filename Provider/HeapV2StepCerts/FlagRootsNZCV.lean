-- for Memory: TST Xn, #7 with its full NZCV, the B1b root (H-P2 N/C/V at 351).
import HeapV2StepCerts.FlagRoots
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1000000
namespace HeapV2StepCerts.FlagRoots.TstF4
open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots

theorem c2_cases (c : BitVec 2) : c = 0#2 ∨ c = 1#2 ∨ c = 2#2 ∨ c = 3#2 := by
  rcases c with ⟨⟨n, hn⟩⟩
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp <;> decide

/-- PSTATE.N: bit 3 of `N ++ Z ++ CV`. -/
theorem exN (a b : BitVec 1) (c : BitVec 2) : Sail.BitVec.extractLsb (a ++ b ++ c) 3 3 = a := by
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases b with rfl | rfl <;>
    rcases c2_cases c with rfl | rfl | rfl | rfl <;> decide
/-- PSTATE.C: bit 1. -/
theorem exC (a b : BitVec 1) (c : BitVec 2) : Sail.BitVec.extractLsb (a ++ b ++ c) 1 1 = Sail.BitVec.extractLsb c 1 1 := by
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases b with rfl | rfl <;>
    rcases c2_cases c with rfl | rfl | rfl | rfl <;> decide
/-- PSTATE.V: bit 0. -/
theorem exV (a b : BitVec 1) (c : BitVec 2) : Sail.BitVec.extractLsb (a ++ b ++ c) 0 0 = Sail.BitVec.extractLsb c 0 0 := by
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases b with rfl | rfl <;>
    rcases c2_cases c with rfl | rfl | rfl | rfl <;> decide

/-- `[i]!` of an AND is the AND of the bits (width-polymorphic, so it unifies at any elaborated width). -/
theorem bang_and {w : Nat} (x y : BitVec w) (i : Nat) : (x &&& y)[i]! = (x[i]! && y[i]!) := by
  by_cases h : i < w
  · rw [getElem!_pos (x &&& y) i h, getElem!_pos x i h, getElem!_pos y i h, BitVec.getElem_and]
  · rw [getElem!_neg (x &&& y) i h, getElem!_neg x i h, getElem!_neg y i h]; rfl

theorem join1_false : (BitVec.ofBoolListBE (List.map (fun b : BitVec 1 => b[0]) [BitVec.ofBool false])).toNat = 0 := by
  decide

/-- The N-flag shape: the one-bit join of bit `i` of `x &&& y` is 0 when bit `i` of `y` is clear. -/
theorem n_zero {w : Nat} (x y : BitVec w) (i : Nat) (hy : y[i]! = false)
    (c : (List.map (fun b : BitVec 1 => b[0]) [BitVec.ofBool (x &&& y)[i]!]).length = 1) :
    BitVec.cast c (BitVec.ofBoolListBE (List.map (fun b : BitVec 1 => b[0]) [BitVec.ofBool (x &&& y)[i]!])) = 0#1 := by
  rw [bang_and, hy, Bool.and_false]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_cast]
  exact join1_false

set_option maxHeartbeats 400000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rn : BitVec 5) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s

set_option maxHeartbeats 400000 in
theorem key (s : ArmBridge.Draft.NativeState) (Rn : BitVec 5) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rn = .ok (s.regs.gpr, s.regs.SP_EL0, 0#1,
      (if s.regs.gpr[(GPRSummary.key Rn.toNat).val] &&& 7#64 = 0#64 then 1#1 else 0#1), 0#1, 0#1) u := by
  unfold native
  simp only [hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr, ArmFull.Register.PSTATE_set]
  apply ok_congr
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = xn
  simp only [Prod.mk.injEq, exA, exN, exC, exV, true_and]
  simp [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, Sail.Int.toNatChecked, IsZeroBit, IsZero, xcast]
  refine ⟨?_, ?_⟩
  · rw [xcast]
    simp only [BitVec.access, BitVec.join1]
    apply n_zero
    decide
  · split <;> split <;> rename_i h1 h2 <;> (try rfl) <;> exfalso <;> simp only [BEq.beq, decide_eq_true_eq] at h1
    · exact h2 h1
    · exact h1 h2

/-- TstF.flags' four conjuncts verbatim, then N = C = V = 0 (ANDS imm mask 7: bit 63 clear; logical ops clear C, V). -/
theorem flags (s : ArmBridge.Draft.NativeState) (Rn : BitVec 5) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRn : ¬ (Rn.toNat : Int) = 31) :
    (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s =
      .ok () (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)) ∧
    (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.gpr = s.regs.gpr ∧
    (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.SP_EL0 = s.regs.SP_EL0 ∧
    ((ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.PSTATE.Z = 1#1 ↔
      s.regs.gpr[(GPRSummary.key Rn.toNat).val] &&& 7#64 = 0#64) ∧
    (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.PSTATE.N = 0#1 ∧
    (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.PSTATE.C = 0#1 ∧
    (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.PSTATE.V = 0#1 := by
  obtain ⟨u, hu⟩ := key s Rn hRn
  have hc := (complete s Rn rn el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s _ hc
  exact ⟨h1, congrArg Prod.fst h2, congrArg (fun p => p.2.1) h2,
    (Eq.to_iff (congrArg (fun p => p.2.2.2.1 = 1#1) h2)).trans (ite_one _),
    congrArg (fun p => p.2.2.1) h2, congrArg (fun p => p.2.2.2.2.1) h2, congrArg (fun p => p.2.2.2.2.2) h2⟩

#print axioms key
#print axioms flags
end HeapV2StepCerts.FlagRoots.TstF4
