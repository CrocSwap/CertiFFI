-- Memory (certiffi P1): value roots for the flag setters and the loop counter: SUBS-imm (Z, C, Xd),
-- CMP-imm (Z, C), TST-imm (Z), MOVZ (Xd), as one-field drive_spec roots of the class actions.
import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
import Bridge.RootFrame
import Bridge.CruxCore
import HeapV2StepCerts.RegRootsB
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1000000
namespace HeapV2StepCerts.FlagRoots
open HeapV2StepCerts.RegRoots

theorem bv1_cases (a : BitVec 1) : a = 0#1 ∨ a = 1#1 := by
  rcases a with ⟨⟨n, hn⟩⟩
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl <;> simp <;> decide
theorem ex2 (a b c d : BitVec 1) : Sail.BitVec.extractLsb (a ++ b ++ c ++ d) 2 2 = b := by
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases b with rfl | rfl <;>
    rcases bv1_cases c with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;> decide
theorem ex1 (a b c d : BitVec 1) : Sail.BitVec.extractLsb (a ++ b ++ c ++ d) 1 1 = c := by
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases b with rfl | rfl <;>
    rcases bv1_cases c with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;> decide
theorem xcast (xn : BitVec 64) : BitVec.extractLsb 63 0 xn = xn := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.extractLsb'_toNat]
theorem ok_congr {α σ ε : Type} {a b : α} {u : σ} (h : a = b) :
    ∃ u' : σ, (EStateM.Result.ok a u : EStateM.Result ε σ α) = EStateM.Result.ok b u' := ⟨u, h ▸ rfl⟩
theorem ite_one (P : Prop) [Decidable P] : ((if P then 1#1 else 0#1) = 1#1) ↔ P := by
  split <;> simp_all

theorem exA (a b : BitVec 1) (c : BitVec 2) : Sail.BitVec.extractLsb (a ++ b ++ c) 2 2 = b := by
  have hc : c = 0#2 ∨ c = 1#2 ∨ c = 2#2 ∨ c = 3#2 := by
    rcases c with ⟨⟨n, hn⟩⟩
    have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp <;> decide
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases b with rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;> decide

/-! ### SUBS Xd, Xn, #imm (Rd ≠ 31) -/
namespace SubsF
set_option maxHeartbeats 400000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z, u.regs.PSTATE.C)) : SailM _) s

set_option maxHeartbeats 400000 in
theorem key (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rd Rn imm12 = .ok
    (s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64) (GPRSummary.key Rd.toNat).isLt,
     s.regs.SP_EL0,
     (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat = imm12.toNat then 1#1 else 0#1),
     (if imm12.toNat ≤ (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat then 1#1 else 0#1)) u := by
  unfold native
  simp only [hRd, hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr]
  apply ok_congr
  simp only [ArmFull.Register.PSTATE_set]
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = xn
  simp only [Prod.mk.injEq, ex1, ex2, true_and]
  dsimp only [BitVec.length]
  generalize hk : (~~~Sail.BitVec.zeroExtend imm12 (Sail.Int.toNatChecked 64)) = nimm
  have hval : (nimm.toNat : Int) = 18446744073709551615 - (imm12.toNat : Int) := by
    subst hk
    have : imm12.toNat < 4096 := imm12.isLt
    show ((~~~(BitVec.setWidth 64 imm12)).toNat : Int) = _
    rw [BitVec.toNat_not, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    omega
  have ha := xn.isLt
  have hb : imm12.toNat < 4096 := imm12.isLt
  simp [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, Sail.BitVec.zeroExtend, Sail.Int.toNatChecked, integer_subrange, get_slice_int, IsZero, xcast]
  simp only [Sail.Int.toNatChecked] at hval
  refine ⟨?_, ?_, ?_⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_sub, BitVec.toNat_setWidth, Sail.Int.toNatChecked]
    omega
  · split <;> split <;> rename_i h1 h2 <;> (try rfl) <;> exfalso
    · have e := congrArg BitVec.toNat (beq_iff_eq.mp h1)
      simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_ofNat, Sail.Int.toNatChecked] at e
      omega
    · simp only [BEq.beq, decide_eq_true_eq] at h1
      apply h1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_ofNat, Sail.Int.toNatChecked]
      omega
  · split <;> split <;> rename_i h1 h2 <;> (try rfl) <;> exfalso <;> omega

theorem flags (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s =
      .ok () (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)) ∧
    (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)).regs.gpr =
      s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64) (GPRSummary.key Rd.toNat).isLt ∧
    (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)).regs.SP_EL0 = s.regs.SP_EL0 ∧
    ((ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)).regs.PSTATE.Z = 1#1 ↔
      (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat = imm12.toNat) ∧
    ((ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)).regs.PSTATE.C = 1#1 ↔
      imm12.toNat ≤ (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat) := by
  obtain ⟨u, hu⟩ := key s Rd Rn imm12 hRd hRn
  have hc := (complete s Rd Rn imm12 rd rn el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z, u.regs.PSTATE.C)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z, u.regs.PSTATE.C)) s _ hc
  refine ⟨h1, congrArg Prod.fst h2, congrArg (fun p => p.2.1) h2, ?_, ?_⟩
  · exact (Eq.to_iff (congrArg (fun p => p.2.2.1 = 1#1) h2)).trans (ite_one _)
  · exact (Eq.to_iff (congrArg (fun p => p.2.2.2 = 1#1) h2)).trans (ite_one _)

#print axioms flags
end SubsF

/-! ### CMP Xn, #imm (SUBS with Rd = 31) -/
namespace CmpF
set_option maxHeartbeats 400000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rn : BitVec 5) (imm12 : BitVec 12) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z, u.regs.PSTATE.C)) : SailM _) s

set_option maxHeartbeats 400000 in
theorem key (s : ArmBridge.Draft.NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rn imm12 = .ok
    (s.regs.gpr, s.regs.SP_EL0,
     (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat = imm12.toNat then 1#1 else 0#1),
     (if imm12.toNat ≤ (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat then 1#1 else 0#1)) u := by
  unfold native
  simp only [hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr]
  apply ok_congr
  simp only [ArmFull.Register.PSTATE_set]
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = xn
  simp only [Prod.mk.injEq, ex1, ex2, true_and]
  dsimp only [BitVec.length]
  generalize hk : (~~~Sail.BitVec.zeroExtend imm12 (Sail.Int.toNatChecked 64)) = nimm
  have hval : (nimm.toNat : Int) = 18446744073709551615 - (imm12.toNat : Int) := by
    subst hk
    have : imm12.toNat < 4096 := imm12.isLt
    show ((~~~(BitVec.setWidth 64 imm12)).toNat : Int) = _
    rw [BitVec.toNat_not, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    omega
  have ha := xn.isLt
  have hb : imm12.toNat < 4096 := imm12.isLt
  simp [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, Sail.Int.toNatChecked, integer_subrange, get_slice_int, IsZero, xcast]
  simp only [Sail.Int.toNatChecked] at hval
  refine ⟨?_, ?_⟩
  · split <;> split <;> rename_i h1 h2 <;> (try rfl) <;> exfalso
    · have e := congrArg BitVec.toNat (beq_iff_eq.mp h1)
      simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_ofNat, Sail.Int.toNatChecked] at e
      omega
    · simp only [BEq.beq, decide_eq_true_eq] at h1
      apply h1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_ofNat, Sail.Int.toNatChecked]
      omega
  · split <;> split <;> rename_i h1 h2 <;> (try rfl) <;> exfalso <;> omega

theorem flags (s : ArmBridge.Draft.NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRn : ¬ (Rn.toNat : Int) = 31) :
    (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s =
      .ok () (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)) ∧
    (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)).regs.gpr = s.regs.gpr ∧
    (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)).regs.SP_EL0 = s.regs.SP_EL0 ∧
    ((ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)).regs.PSTATE.Z = 1#1 ↔
      (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat = imm12.toNat) ∧
    ((ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)).regs.PSTATE.C = 1#1 ↔
      imm12.toNat ≤ (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat) := by
  obtain ⟨u, hu⟩ := key s Rn imm12 hRn
  have hc := (complete s Rn imm12 rn el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z, u.regs.PSTATE.C)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z, u.regs.PSTATE.C)) s _ hc
  refine ⟨h1, congrArg Prod.fst h2, congrArg (fun p => p.2.1) h2, ?_, ?_⟩
  · exact (Eq.to_iff (congrArg (fun p => p.2.2.1 = 1#1) h2)).trans (ite_one _)
  · exact (Eq.to_iff (congrArg (fun p => p.2.2.2 = 1#1) h2)).trans (ite_one _)

#print axioms flags
end CmpF

/-! ### TST Xn, #7 (ANDS with Rd = 31) -/
namespace TstF
set_option maxHeartbeats 400000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rn : BitVec 5) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z)) : SailM _) s

set_option maxHeartbeats 400000 in
theorem key (s : ArmBridge.Draft.NativeState) (Rn : BitVec 5) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rn = .ok (s.regs.gpr, s.regs.SP_EL0,
      (if s.regs.gpr[(GPRSummary.key Rn.toNat).val] &&& 7#64 = 0#64 then 1#1 else 0#1)) u := by
  unfold native
  simp only [hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr, ArmFull.Register.PSTATE_set]
  apply ok_congr
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = xn
  simp only [Prod.mk.injEq, exA, true_and]
  simp [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, Sail.Int.toNatChecked, IsZeroBit, IsZero, xcast]
  split <;> split <;> rename_i h1 h2 <;> (try rfl) <;> exfalso <;> simp only [BEq.beq, decide_eq_true_eq] at h1
  · exact h2 h1
  · exact h1 h2

theorem flags (s : ArmBridge.Draft.NativeState) (Rn : BitVec 5) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRn : ¬ (Rn.toNat : Int) = 31) :
    (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s =
      .ok () (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)) ∧
    (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.gpr = s.regs.gpr ∧
    (ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.SP_EL0 = s.regs.SP_EL0 ∧
    ((ArmBridge.CruxCore.resSt s ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) s)).regs.PSTATE.Z = 1#1 ↔
      s.regs.gpr[(GPRSummary.key Rn.toNat).val] &&& 7#64 = 0#64) := by
  obtain ⟨u, hu⟩ := key s Rn hRn
  have hc := (complete s Rn rn el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.Z)) s _ hc
  exact ⟨h1, congrArg Prod.fst h2, congrArg (fun p => p.2.1) h2,
    (Eq.to_iff (congrArg (fun p => p.2.2 = 1#1) h2)).trans (ite_one _)⟩

#print axioms flags

end TstF

/-! ### MOVZ Xd, #32 -/
namespace MovzF
theorem key (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) :
    ∃ u, RegRoots.Movz64z.regs_native s Rd 32#16 = .ok
      (s.regs.gpr.set (GPRSummary.key Rd.toNat).val 32#64 (GPRSummary.key Rd.toNat).isLt, s.regs.SP_EL0) u := by
  unfold RegRoots.Movz64z.regs_native
  simp only [hRd, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr]
  apply ok_congr
  simp only [Prod.mk.injEq, and_true]
  congr 1

theorem regs (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (rd : Rd.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) :
    (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd 32#16 0#2 2#2 1#1 : SailM Unit) s =
      .ok () (ArmBridge.CruxCore.resSt s ((decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd 32#16 0#2 2#2 1#1 : SailM Unit) s)) ∧
    (ArmBridge.CruxCore.resSt s ((decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd 32#16 0#2 2#2 1#1 : SailM Unit) s)).regs.gpr =
      s.regs.gpr.set (GPRSummary.key Rd.toNat).val 32#64 (GPRSummary.key Rd.toNat).isLt ∧
    (ArmBridge.CruxCore.resSt s ((decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd 32#16 0#2 2#2 1#1 : SailM Unit) s)).regs.SP_EL0 = s.regs.SP_EL0 := by
  obtain ⟨u, hu⟩ := key s Rd hRd
  have hc := (RegRoots.Movz64z.regs_complete s Rd 32#16 rd el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0)) s _ hc
  exact ⟨h1, congrArg Prod.fst h2, congrArg Prod.snd h2⟩

#print axioms regs
end MovzF

/-! ### MOVZ Xd, #0 -/
namespace MovzF0
theorem key (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) :
    ∃ u, RegRoots.Movz64z.regs_native s Rd 0#16 = .ok
      (s.regs.gpr.set (GPRSummary.key Rd.toNat).val 0#64 (GPRSummary.key Rd.toNat).isLt, s.regs.SP_EL0) u := by
  unfold RegRoots.Movz64z.regs_native
  simp only [hRd, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr]
  apply ok_congr
  simp only [Prod.mk.injEq, and_true]
  congr 1

theorem regs (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (rd : Rd.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) :
    (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd 0#16 0#2 2#2 1#1 : SailM Unit) s =
      .ok () (ArmBridge.CruxCore.resSt s ((decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd 0#16 0#2 2#2 1#1 : SailM Unit) s)) ∧
    (ArmBridge.CruxCore.resSt s ((decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd 0#16 0#2 2#2 1#1 : SailM Unit) s)).regs.gpr =
      s.regs.gpr.set (GPRSummary.key Rd.toNat).val 0#64 (GPRSummary.key Rd.toNat).isLt ∧
    (ArmBridge.CruxCore.resSt s ((decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd 0#16 0#2 2#2 1#1 : SailM Unit) s)).regs.SP_EL0 = s.regs.SP_EL0 := by
  obtain ⟨u, hu⟩ := key s Rd hRd
  have hc := (RegRoots.Movz64z.regs_complete s Rd 0#16 rd el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0)) s _ hc
  exact ⟨h1, congrArg Prod.fst h2, congrArg Prod.snd h2⟩

#print axioms regs
end MovzF0
end HeapV2StepCerts.FlagRoots
