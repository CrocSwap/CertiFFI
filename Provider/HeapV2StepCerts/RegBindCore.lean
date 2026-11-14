-- Memory ((c)): register-content binding for the heap-v2 normal path.
-- Generic part: registers, binding lists (r = pin + c), symbolic per-step updates and the
-- carry lemma. Plan tables and their decide checks are generated (RegBindData).
import ArmFull.Defs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace HeapV2StepCerts.RegBind

/-- The native state (= ArmBridge.Draft.St, reducible); light import on purpose. -/
abbrev St := SequentialState ArmFull.Regs oracleChoiceSource

inductive Reg where
  | x (i : Fin 31)
  | sp
  deriving DecidableEq, Repr

def regVal (s : St) : Reg → BitVec 64
  | .x i => s.regs.gpr[i.val]
  | .sp => s.regs.SP_EL0

inductive Upd where
  | keep
  | set (src : Reg) (c : Int)
  | drop
  deriving DecidableEq, Repr

abbrev Bind := Reg × Nat × Int

/-- Bindings hold for the pin values pinv (instantiated with HeapV2E17.pin p in RegBind). -/
def BindsHold (pinv : Nat → Nat) (bs : List Bind) (s : St) : Prop :=
  ∀ b ∈ bs, regVal s b.1 = BitVec.ofInt 64 ((pinv b.2.1 : Int) + b.2.2)

def updOf (us : List (Reg × Upd)) (r : Reg) : Upd := ((us.find? (·.1 = r)).map (·.2)).getD .keep

/-- The actual register effect of one step, for the symbolic update `us`. -/
def Holds (us : List (Reg × Upd)) (x y : St) : Prop :=
  ∀ r, match updOf us r with
    | .keep => regVal y r = regVal x r
    | .set s c => regVal y r = regVal x s + BitVec.ofInt 64 c
    | .drop => True

/-- `b` is derivable at the next step from bindings `bs` under updates `us`. -/
def Derives (us : List (Reg × Upd)) (bs : List Bind) (b : Bind) : Bool :=
  match updOf us b.1 with
  | .keep => bs.contains b
  | .set s c => bs.any fun b' => b'.1 == s && b'.2.1 == b.2.1 && b'.2.2 + c == b.2.2
  | .drop => false

theorem carry {p : Nat → Nat} {us : List (Reg × Upd)} {bs bs' : List Bind} {x y : St}
    (derives : bs'.all (Derives us bs) = true) (holds : Holds us x y) (bound : BindsHold p bs x) :
    BindsHold p bs' y := by
  intro b member
  have d := List.all_eq_true.1 derives b member
  have h := holds b.1
  unfold Derives at d
  split at d
  · next hk =>
    rw [hk] at h; rw [h]
    exact bound b (List.contains_iff_mem.1 d)
  · next s c hs =>
    rw [hs] at h; rw [h]
    obtain ⟨b', mem', cond⟩ := List.any_eq_true.1 d
    simp only [Bool.and_eq_true, beq_iff_eq] at cond
    obtain ⟨⟨hs', hp⟩, hc⟩ := cond
    rw [← hs', bound b' mem', ← BitVec.ofInt_add, hp, ← hc, Int.add_assoc]
  · simp at d

/-- Gpr/SP unchanged (branches, compares, stores without writeback): keep-only update. -/
theorem holds_of_regs_eq {us : List (Reg × Upd)} {x y : St}
    (keepOnly : ∀ r, updOf us r = .keep ∨ updOf us r = .drop)
    (gpr : y.regs.gpr = x.regs.gpr) (sp : y.regs.SP_EL0 = x.regs.SP_EL0) : Holds us x y := by
  intro r
  rcases keepOnly r with h | h <;> rw [h]
  · cases r with
    | x i => simp only [regVal, gpr]
    | sp => simp only [regVal, sp]
  · trivial

/-- Compose with a prefix that leaves GPRs and SP alone (e.g. the actual fetch). -/
theorem Holds.of_prefix {us : List (Reg × Upd)} {x f y : St}
    (gpr : f.regs.gpr = x.regs.gpr) (sp : f.regs.SP_EL0 = x.regs.SP_EL0) (h : Holds us f y) : Holds us x y := by
  have rv : ∀ r, regVal f r = regVal x r := by
    intro r; cases r with
    | x i => simp only [regVal, gpr]
    | sp => simp only [regVal, sp]
  intro r
  have hr := h r
  split at hr <;> simp only [*] at * <;> first | trivial | (rw [hr, rv]) | (rw [hr, rv])

#print axioms carry
end HeapV2StepCerts.RegBind
