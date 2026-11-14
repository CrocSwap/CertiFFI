-- Memory ((c1/c2)): RegBind semantics over the generated plan tables.
import HeapV2StepCerts.RegBindData
import ArmCertTranslateModel.HeapV2E17Table
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxRecDepth 4096
namespace HeapV2StepCerts.RegBind
open ArmBridge.Draft

/-- RegBind at plan step k for entry pins p. -/
def RegBind (p : HeapV2E17.Pins) (k : Nat) (s : NativeState) : Prop := BindsHold (HeapV2E17.pin p) (binds k) s

/-- Every plan access is the bound base register plus the access offset. -/
def accessCheck (e : Nat × Nat × Int × Nat × Bool) : Bool :=
  accessTable.any fun a => a.1 == e.1 && (binds e.1).any fun b => b.1 == a.2.1 && b.2.1 == e.2.1 && b.2.2 + a.2.2 == e.2.2.1

theorem accesses_ok : HeapV2Plan.symbolicAccesses.all accessCheck = true := by decide +kernel

/-- c2: one step carries the binding, given the step's actual register effect. -/
theorem carry_step {p : HeapV2E17.Pins} {k : Nat} (hk : k < 358) {x y : NativeState}
    (holds : Holds (upds k) x y) (bound : RegBind p k x) : RegBind p (k + 1) y :=
  carry (table_ok k hk) holds bound

/-- c1: at a memory step, the plan access VA is the bound base register plus the offset. -/
theorem access_va {p : HeapV2E17.Pins} {s : NativeState} {e : Nat × Nat × Int × Nat × Bool}
    (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 s) :
    ∃ a ∈ accessTable, a.1 = e.1 ∧ regVal s a.2.1 + BitVec.ofInt 64 a.2.2 = HeapV2E17.dataVA p e := by
  have chk := List.all_eq_true.1 accesses_ok e member
  obtain ⟨a, mem, cond⟩ := List.any_eq_true.1 chk
  simp only [Bool.and_eq_true, beq_iff_eq] at cond
  obtain ⟨hk, hb⟩ := cond
  obtain ⟨b, bmem, bcond⟩ := List.any_eq_true.1 hb
  simp only [Bool.and_eq_true, beq_iff_eq] at bcond
  obtain ⟨⟨hr, hp⟩, hc⟩ := bcond
  refine ⟨a, mem, hk, ?_⟩
  rw [← hr, bound b bmem, ← BitVec.ofInt_add, hp, Int.add_assoc, hc]
  rfl

/-- Entry: SP / X0 / X1 hold the pins. -/
theorem initial {p : HeapV2E17.Pins} {s : NativeState}
    (sp : s.regs.SP_EL0 = BitVec.ofInt 64 (p.sp : Int))
    (x0 : regVal s (.x 0) = BitVec.ofInt 64 (p.x0 : Int))
    (x1 : regVal s (.x 1) = BitVec.ofInt 64 (p.x1 : Int)) : RegBind p 0 s := by
  intro b member
  rw [show binds 0 = _ from binds_zero] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with h | h | h <;> subst h
  · simpa [regVal, HeapV2E17.pin] using sp
  · simpa [HeapV2E17.pin] using x0
  · simpa [HeapV2E17.pin] using x1

#print axioms carry_step
#print axioms access_va
#print axioms initial
end HeapV2StepCerts.RegBind
