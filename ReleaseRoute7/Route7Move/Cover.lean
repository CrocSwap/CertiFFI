-- Route 7 memmove fetched-PC coverage (loops, over Route7Move port): every state the memmove run passes
-- through is at a reviewed memmove word (0x1e4 + 4j, j < 21) or, after the final RET, at returnPC. AUX, never a premise.
import CT1.Route7Word
import Route7Move.Context
import Route7Copy.Cover
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace Route7Move
open ArmCertLoop ArmCertLoop.ContractDraft

/-- The memmove PC set: a reviewed memmove word, or returnPC (after the final RET). -/
def PcOkM (c : Context) (x : NativeState) : Prop :=
  (x.regs._PC = c.returnPC ∨
    ∃ j, j < 21 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memmove_entry + 4 * j)) ∧
  CT1.Route7Word.ImageWords c.mapping c.base 16 21 x

/-- Every word offset of every memmove path schedule is one of the 21 memmove words. -/
theorem moveWordOffset_word (p : Schedule.MovePath) (n k : Nat) :
    ∃ j, j < 21 ∧ Schedule.moveWordOffset p n k = 4 * j := by
  cases p <;> simp only [Schedule.moveWordOffset]
  · split
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨12, by decide, rfl⟩
  · split
    · exact ⟨k, by omega, rfl⟩
    · exact ⟨12, by decide, rfl⟩
  · split
    · exact ⟨k, by omega, rfl⟩
    · split
      · exact ⟨13, by decide, rfl⟩
      · split
        · exact ⟨14 + (k - 5) % 6, by omega, by omega⟩
        · exact ⟨20, by decide, rfl⟩
  · split
    · exact ⟨k, by omega, rfl⟩
    · split
      · exact ⟨6 + (k - 6) % 6, by omega, by omega⟩
      · exact ⟨12, by decide, rfl⟩

theorem pcOk_of_pc_m (c : Context) (k : Nat) (x : NativeState)
    (pc : x.regs._PC = c.base + Route7Move.offset c k) :
    (x.regs._PC = c.returnPC ∨
    ∃ j, j < 21 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memmove_entry + 4 * j)) := by
  by_cases last : k = c.budget
  · left
    rw [pc]
    simp only [Route7Move.offset, Schedule.nativeOffset, if_pos last]
    bv_omega
  · right
    obtain ⟨j, hj, word⟩ := moveWordOffset_word c.path c.n k
    refine ⟨j, hj, ?_⟩
    rw [pc]
    simp only [Route7Move.offset, Schedule.nativeOffset, if_neg last, word, MemReloc.imageAddress]

theorem pcOk_of_env_m (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat)
    (x : NativeState) (env : EnvM c catalogue entry k x) : PcOkM c x :=
  ⟨pcOk_of_pc_m c k x env.core.v1.pc,
    CT1.Route7Word.imageWords_of_placed env.core.placed 16 21 (by decide)⟩


/-- CT1 R-a: at a non-final tick the PC is one of the routine's words. -/
theorem wordPc_of_pc_m (c : Context) (k : Nat) (hk : k ≠ c.budget) (x : NativeState)
    (pc : x.regs._PC = c.base + Route7Move.offset c k) :
    ∃ j, j < 21 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memmove_entry + 4 * j) := by
  obtain ⟨j, hj, word⟩ := moveWordOffset_word c.path c.n k
  refine ⟨j, hj, ?_⟩
  rw [pc]
  simp only [Route7Move.offset, Schedule.nativeOffset, if_neg hk, word, MemReloc.imageAddress]

end Route7Move
#print axioms Route7Move.moveWordOffset_word
#print axioms Route7Move.pcOk_of_env_m
