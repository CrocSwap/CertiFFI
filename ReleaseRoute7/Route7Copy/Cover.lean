-- Route 7 unit 3 coverage (loops): fetched-PC coverage over EnvR. Every state the memcpy run passes through is at a
-- reviewed memcpy word (0x1a4 + 4j, j < 9) or, after the final RET, at returnPC. AUX, never a caller premise.
import CT1.Route7Word
import Route7Copy.Context
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace Route7Copy
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft

/-- The memcpy PC set: a reviewed memcpy word, or returnPC (after the final RET). -/
def PcOk (c : Context) (x : NativeState) : Prop :=
  (x.regs._PC = c.returnPC ∨
    ∃ j, j < 9 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memcpy_entry + 4 * j)) ∧
  CT1.Route7Word.ImageWords c.mapping c.base 0 9 x

/-- Every word offset of the copy schedule is one of the 9 memcpy words. -/
theorem copyWordOffset_word (n k : Nat) : ∃ j, j < 9 ∧ Schedule.copyWordOffset n k = 4 * j := by
  unfold Schedule.copyWordOffset
  split
  · exact ⟨0, by decide, rfl⟩
  · split
    · exact ⟨8, by decide, rfl⟩
    · split
      · exact ⟨1, by decide, rfl⟩
      · split
        · exact ⟨2 + (k - 2) % 6, by omega, by omega⟩
        · exact ⟨8, by decide, rfl⟩

/-- PcOk from the invariant's PC equation at any tick of the copy schedule. -/
theorem pcOk_of_pc (c : Context) (k : Nat) (x : NativeState)
    (pc : x.regs._PC = c.base + offset c.base c.returnPC c.n k) :
    (x.regs._PC = c.returnPC ∨
    ∃ j, j < 9 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memcpy_entry + 4 * j)) := by
  by_cases last : k = Schedule.copySteps c.n
  · left
    rw [pc]
    simp only [offset, Schedule.nativeOffset, if_pos last]
    bv_omega
  · right
    obtain ⟨j, hj, word⟩ := copyWordOffset_word c.n k
    refine ⟨j, hj, ?_⟩
    rw [pc]
    simp only [offset, Schedule.nativeOffset, if_neg last, word, MemReloc.imageAddress]

/-- PcOk from EnvR at any tick. -/
theorem pcOk_of_env (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat)
    (x : NativeState) (env : EnvR c catalogue entry k x) : PcOk c x :=
  ⟨pcOk_of_pc c k x env.core.v1.pc,
    CT1.Route7Word.imageWords_of_placed env.core.placed 0 9 (by decide)⟩

/-- Every prefix state of a successful `ticks`-step run from `x` satisfies `P`. -/
def Covered (real : Type) [Sail.SailReal real] (P : NativeState → Prop) (ticks : Nat) (x : NativeState) : Prop :=
  ∀ k, k ≤ ticks → ∃ z, Uget.Chain.modelRun real k x = .ok () z ∧ P z

theorem covered_zero (real : Type) [Sail.SailReal real] (P : NativeState → Prop) (x : NativeState) (px : P x) :
    Covered real P 0 x := by
  intro k hk
  have : k = 0 := by omega
  subst this
  exact ⟨x, rfl, px⟩

theorem covered_append (real : Type) [Sail.SailReal real] (P : NativeState → Prop)
    (n m : Nat) (x y : NativeState) (run : Uget.Chain.modelRun real n x = .ok () y)
    (first : Covered real P n x) (second : Covered real P m y) : Covered real P (n + m) x := by
  intro k hk
  by_cases low : k ≤ n
  · exact first k low
  · obtain ⟨z, rz, pz⟩ := second (k - n) (by omega)
    refine ⟨z, ?_, pz⟩
    have := Aux.modelRun_append real n (k - n) x y z run rz
    simpa only [Nat.add_sub_cancel' (Nat.le_of_lt (Nat.lt_of_not_le low))] using this

/-- One step from x to y with P at both ends covers the 1-step run. -/
theorem covered_one (real : Type) [Sail.SailReal real] (P : NativeState → Prop) (x y : NativeState)
    (run : Uget.Chain.modelRun real 1 x = .ok () y) (px : P x) (py : P y) : Covered real P 1 x := by
  intro k hk
  by_cases zero : k = 0
  · subst zero
    exact ⟨x, rfl, px⟩
  · have : k = 1 := by omega
    subst this
    exact ⟨y, run, py⟩


/-- CT1 R-a: at a non-final tick the PC is one of the routine's words. -/
theorem wordPc_of_pc (c : Context) (k : Nat) (hk : k ≠ Schedule.copySteps c.n) (x : NativeState)
    (pc : x.regs._PC = c.base + offset c.base c.returnPC c.n k) :
    ∃ j, j < 9 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memcpy_entry + 4 * j) := by
  obtain ⟨j, hj, word⟩ := copyWordOffset_word c.n k
  refine ⟨j, hj, ?_⟩
  rw [pc]
  simp only [offset, Schedule.nativeOffset, if_neg hk, word, MemReloc.imageAddress]

end Route7Copy
#print axioms Route7Copy.copyWordOffset_word
#print axioms Route7Copy.pcOk_of_pc
#print axioms Route7Copy.covered_append
#print axioms Route7Copy.covered_one
