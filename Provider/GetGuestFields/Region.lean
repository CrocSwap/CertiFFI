import GetGuestFields.RegionTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false
namespace GetGuestFields.RegionFacts
open S1Normality

theorem bind_run {α β : Type} {p : SailM α} {k : α → SailM β}
    {s t : State} {a : α} (h : p s = .ok a t) : (p >>= k) s = k a t := by
  simp only [Bind.bind, EStateM.bind, h]

def Good (input : S1TTWParams) (tx : BitVec 6) (s : State) :
    EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok wp t => Frame s t ∧ active wp = {active input with tgx := .TGx_4KB, txsz := tx}
  | .error _ _ => False

def TGGood (s : State) : EStateM.Result (Sail.Error exception) State TGx → Prop
  | .ok tg t => Frame s t ∧ tg = .TGx_4KB
  | .error _ _ => False

noncomputable def lowerBody (wp : S1TTWParams) : SailM S1TTWParams := do
  let tcr ← GetGuestReads.read ArmFull.Register.TCR_EL1
  let tg ← GetGuestVirtualization.TG0.native (_get_TCR_EL1_Type_TG0 tcr)
  let wp := {wp with tgx := tg}
  let tcr ← GetGuestReads.read ArmFull.Register.TCR_EL1
  let wp := {wp with txsz := _get_TCR_EL1_Type_T0SZ tcr}
  RegionTail.lower wp

theorem lower_eq (wp : S1TTWParams) :
    GetGuestFields.region wp .VARange_LOWER = lowerBody wp := by
  have hc : (VARange.VARange_LOWER == VARange.VARange_LOWER) = true := rfl
  unfold GetGuestFields.region lowerBody RegionTail.lower
  simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem tg0 (s : State) :
    ∃ t, GetGuestVirtualization.TG0.native 0#2 s = .ok .TGx_4KB t ∧ Frame s t := by
  refine ⟨{s with choiceOcc := s.choiceOcc.insert 1253 (s.choiceOcc.getD 1253 0 + 1)}, ?_, rfl, rfl, rfl⟩
  rfl

theorem lower (wp : S1TTWParams) (tcr : BitVec 64) (s : State)
    (hr : s.regs.bank_BitVec_64 .TCR_EL1 = tcr)
    (htg : _get_TCR_EL1_Type_TG0 tcr = 0#2) :
    Good wp (_get_TCR_EL1_Type_T0SZ tcr) s
      (GetGuestFields.region wp .VARange_LOWER s) := by
  rcases tg0 s with ⟨t, ht, hf⟩
  have hrt : t.regs.bank_BitVec_64 .TCR_EL1 = tcr := by rw [hf.1, hr]
  let updated : S1TTWParams := {wp with tgx := .TGx_4KB, txsz := _get_TCR_EL1_Type_T0SZ tcr}
  rcases RegionTail.lower_returns updated t with ⟨out, u, hout, hfu, hv⟩
  have read0 : GetGuestReads.read ArmFull.Register.TCR_EL1 s = .ok tcr s := by
    change EStateM.Result.ok (s.regs.bank_BitVec_64 .TCR_EL1) s = .ok tcr s
    rw [hr]
  have read1 : GetGuestReads.read ArmFull.Register.TCR_EL1 t = .ok tcr t := by
    change EStateM.Result.ok (t.regs.bank_BitVec_64 .TCR_EL1) t = .ok tcr t
    rw [hrt]
  have prefix_run : lowerBody wp s = RegionTail.lower updated t := by
    unfold lowerBody
    rw [bind_run read0, htg, bind_run ht, bind_run read1]
  rw [lower_eq, prefix_run, hout]
  exact ⟨⟨hfu.1.trans hf.1, hfu.2.1.trans hf.2.1, hfu.2.2.trans hf.2.2⟩,
    by simpa only [updated, active] using hv⟩
#print axioms lower

noncomputable def upperBody (wp : S1TTWParams) : SailM S1TTWParams := do
  let tcr ← GetGuestReads.read ArmFull.Register.TCR_EL1
  let tg ← GetGuestVirtualization.TG1.native (_get_TCR_EL1_Type_TG1 tcr)
  let wp := {wp with tgx := tg}
  let tcr ← GetGuestReads.read ArmFull.Register.TCR_EL1
  let wp := {wp with txsz := _get_TCR_EL1_Type_T1SZ tcr}
  RegionTail.upper wp

theorem upper_eq (wp : S1TTWParams) :
    GetGuestFields.region wp .VARange_UPPER = upperBody wp := by
  have hc : (VARange.VARange_UPPER == VARange.VARange_LOWER) = false := rfl
  unfold GetGuestFields.region upperBody RegionTail.upper
  simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem tg1 (s : State) :
    ∃ t, GetGuestVirtualization.TG1.native 2#2 s = .ok .TGx_4KB t ∧ Frame s t := by
  refine ⟨{s with choiceOcc := s.choiceOcc.insert 1254 (s.choiceOcc.getD 1254 0 + 1)}, ?_, rfl, rfl, rfl⟩
  rfl

theorem upper (wp : S1TTWParams) (tcr : BitVec 64) (s : State)
    (hr : s.regs.bank_BitVec_64 .TCR_EL1 = tcr)
    (htg : _get_TCR_EL1_Type_TG1 tcr = 2#2) :
    Good wp (_get_TCR_EL1_Type_T1SZ tcr) s
      (GetGuestFields.region wp .VARange_UPPER s) := by
  rcases tg1 s with ⟨t, ht, hf⟩
  have hrt : t.regs.bank_BitVec_64 .TCR_EL1 = tcr := by rw [hf.1, hr]
  let updated : S1TTWParams := {wp with tgx := .TGx_4KB, txsz := _get_TCR_EL1_Type_T1SZ tcr}
  rcases RegionTail.upper_returns updated t with ⟨out, u, hout, hfu, hv⟩
  have read0 : GetGuestReads.read ArmFull.Register.TCR_EL1 s = .ok tcr s := by
    change EStateM.Result.ok (s.regs.bank_BitVec_64 .TCR_EL1) s = .ok tcr s
    rw [hr]
  have read1 : GetGuestReads.read ArmFull.Register.TCR_EL1 t = .ok tcr t := by
    change EStateM.Result.ok (t.regs.bank_BitVec_64 .TCR_EL1) t = .ok tcr t
    rw [hrt]
  have prefix_run : upperBody wp s = RegionTail.upper updated t := by
    unfold upperBody
    rw [bind_run read0, htg, bind_run ht, bind_run read1]
  rw [upper_eq, prefix_run, hout]
  exact ⟨⟨hfu.1.trans hf.1, hfu.2.1.trans hf.2.1, hfu.2.2.trans hf.2.2⟩,
    by simpa only [updated, active] using hv⟩
#print axioms upper
end GetGuestFields.RegionFacts
