import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2MapVPM
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State (BitVec 16)
drive_spec native0, eq0 : fun (v : Int) (s : State)
    (h : fdiv_int v 4 = 0) => mapvpmw v s
drive_spec native1, eq1 : fun (v : Int) (s : State)
    (h : fdiv_int v 4 = 1) => mapvpmw v s
drive_spec native2, eq2 : fun (v : Int) (s : State)
    (h : fdiv_int v 4 = 2) => mapvpmw v s
drive_spec native3, eq3 : fun (v : Int) (s : State)
    (h : fdiv_int v 4 = 3) => mapvpmw v s
drive_spec native4, eq4 : fun (v : Int) (s : State)
    (h : fdiv_int v 4 = 4) => mapvpmw v s
drive_spec native5, eq5 : fun (v : Int) (s : State)
    (h : fdiv_int v 4 = 5) => mapvpmw v s
drive_spec native6, eq6 : fun (v : Int) (s : State)
    (h : fdiv_int v 4 = 6) => mapvpmw v s
drive_spec native7, eq7 : fun (v : Int) (s : State)
    (h : fdiv_int v 4 = 7) => mapvpmw v s
drive_spec nativeNeg, eqNeg : fun (v : Int) (n : Nat) (s : State)
    (h : fdiv_int v 4 = Int.negSucc n) => mapvpmw v s
drive_spec nativeLarge, eqLarge : fun (v : Int) (n : Nat) (s : State)
    (h : fdiv_int v 4 = Int.ofNat (n + 8)) => mapvpmw v s
theorem neg_same (v : Int) (n : Nat) (s : State) : nativeNeg v n s = nativeNeg v 0 s := by
  delta nativeNeg
  rfl
theorem large_same (v : Int) (n : Nat) (s : State) : nativeLarge v n s = nativeNeg v 0 s := by
  delta nativeLarge nativeNeg
  rfl
noncomputable def native (v : Int) (s : State) : Result :=
  if fdiv_int v 4 = 0 then native0 v s else
  if fdiv_int v 4 = 1 then native1 v s else
  if fdiv_int v 4 = 2 then native2 v s else
  if fdiv_int v 4 = 3 then native3 v s else
  if fdiv_int v 4 = 4 then native4 v s else
  if fdiv_int v 4 = 5 then native5 v s else
  if fdiv_int v 4 = 6 then native6 v s else
  if fdiv_int v 4 = 7 then native7 v s else
  nativeNeg v 0 s

theorem complete (v : Int) (s : State) : mapvpmw v s = native v s := by
  by_cases h0 : fdiv_int v 4 = 0
  · simpa [native, h0] using eq0 v s h0
  by_cases h1 : fdiv_int v 4 = 1
  · simpa [native, h1] using eq1 v s h1
  by_cases h2 : fdiv_int v 4 = 2
  · simpa [native, h2] using eq2 v s h2
  by_cases h3 : fdiv_int v 4 = 3
  · simpa [native, h3] using eq3 v s h3
  by_cases h4 : fdiv_int v 4 = 4
  · simpa [native, h4] using eq4 v s h4
  by_cases h5 : fdiv_int v 4 = 5
  · simpa [native, h5] using eq5 v s h5
  by_cases h6 : fdiv_int v 4 = 6
  · simpa [native, h6] using eq6 v s h6
  by_cases h7 : fdiv_int v 4 = 7
  · simpa [native, h7] using eq7 v s h7
  cases hq : fdiv_int v 4 with
  | negSucc n =>
    simpa [native, h0, h1, h2, h3, h4, h5, h6, h7, neg_same] using eqNeg v n s hq
  | ofNat n =>
    have hn0 : n ≠ 0 := by
      intro hn
      apply h0
      simpa [hn] using hq
    have hn1 : n ≠ 1 := by
      intro hn
      apply h1
      simpa [hn] using hq
    have hn2 : n ≠ 2 := by
      intro hn
      apply h2
      simpa [hn] using hq
    have hn3 : n ≠ 3 := by
      intro hn
      apply h3
      simpa [hn] using hq
    have hn4 : n ≠ 4 := by
      intro hn
      apply h4
      simpa [hn] using hq
    have hn5 : n ≠ 5 := by
      intro hn
      apply h5
      simpa [hn] using hq
    have hn6 : n ≠ 6 := by
      intro hn
      apply h6
      simpa [hn] using hq
    have hn7 : n ≠ 7 := by
      intro hn
      apply h7
      simpa [hn] using hq
    have hn : 8 ≤ n := by omega
    have hl : fdiv_int v 4 = Int.ofNat ((n - 8) + 8) := by
      rw [hq]
      congr 1
      omega
    simpa [native, h0, h1, h2, h3, h4, h5, h6, h7, large_same] using eqLarge v (n - 8) s hl
#print axioms complete
noncomputable def word (v : Int) (s : State) : BitVec 64 :=
  if fdiv_int v 4 = 0 then s.regs.bank_BitVec_64 .MPAMVPM0_EL2 else
  if fdiv_int v 4 = 1 then s.regs.bank_BitVec_64 .MPAMVPM1_EL2 else
  if fdiv_int v 4 = 2 then s.regs.bank_BitVec_64 .MPAMVPM2_EL2 else
  if fdiv_int v 4 = 3 then s.regs.bank_BitVec_64 .MPAMVPM3_EL2 else
  if fdiv_int v 4 = 4 then s.regs.bank_BitVec_64 .MPAMVPM4_EL2 else
  if fdiv_int v 4 = 5 then s.regs.bank_BitVec_64 .MPAMVPM5_EL2 else
  if fdiv_int v 4 = 6 then s.regs.bank_BitVec_64 .MPAMVPM6_EL2 else
  if fdiv_int v 4 = 7 then s.regs.bank_BitVec_64 .MPAMVPM7_EL2 else
  0#64

def after (s : State) : State :=
  { s with choiceOcc := s.choiceOcc.insert 758 (s.choiceOcc.getD 758 0 + 1) }

noncomputable def normal (v : Int) (s : State) : Result :=
  .ok (BitVec.slice (word v s) (Sail.Int.toNatChecked (fmod_int v 4 * 16)) 16) (after s)

theorem native_normal (v : Int) (s : State) : native v s = normal v s := by
  by_cases h0 : fdiv_int v 4 = 0
  · simp only [native, normal, word, if_pos h0]
    delta native0 after
    rfl
  by_cases h1 : fdiv_int v 4 = 1
  · simp only [native, normal, word, if_neg h0, if_pos h1]
    delta native1 after
    rfl
  by_cases h2 : fdiv_int v 4 = 2
  · simp only [native, normal, word, if_neg h0, if_neg h1, if_pos h2]
    delta native2 after
    rfl
  by_cases h3 : fdiv_int v 4 = 3
  · simp only [native, normal, word, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
    delta native3 after
    rfl
  by_cases h4 : fdiv_int v 4 = 4
  · simp only [native, normal, word, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    delta native4 after
    rfl
  by_cases h5 : fdiv_int v 4 = 5
  · simp only [native, normal, word, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    delta native5 after
    rfl
  by_cases h6 : fdiv_int v 4 = 6
  · simp only [native, normal, word, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
    delta native6 after
    rfl
  by_cases h7 : fdiv_int v 4 = 7
  · simp only [native, normal, word, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    delta native7 after
    rfl
  simp only [native, normal, word, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  delta nativeNeg after
  rfl

theorem normal_complete (v : Int) (s : State) : mapvpmw v s = normal v s :=
  (complete v s).trans (native_normal v s)
attribute [step_summary] normal_complete
#print axioms normal_complete

end S2MapVPM
