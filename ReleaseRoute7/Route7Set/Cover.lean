-- Route 7 memset fetched-PC coverage (loops, over Route7Set port): every state the memset run passes
-- through is at a reviewed memset word (0x1c8 + 4j, j < 7) or, after the final RET, at returnPC. AUX, never a premise.
import CT1.Route7Word
import Route7Set.Context
import Route7Copy.Cover
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace Route7Set
open ArmCertLoop ArmCertLoop.SetNative ArmCertLoop.ContractDraft

/-- The memset PC set: a reviewed memset word, or returnPC (after the final RET). -/
def PcOkS (c : Context) (x : NativeState) : Prop :=
  (x.regs._PC = c.returnPC ∨
    ∃ j, j < 7 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memset_entry + 4 * j)) ∧
  CT1.Route7Word.ImageWords c.mapping c.base 9 7 x

/-- Every word offset of the memset schedule is one of the 7 memset words. -/
theorem setWordOffset_word (n k : Nat) : ∃ j, j < 7 ∧ Schedule.setWordOffset n k = 4 * j := by
  unfold Schedule.setWordOffset
  split
  · exact ⟨0, by decide, rfl⟩
  · split
    · exact ⟨6, by decide, rfl⟩
    · split
      · exact ⟨1, by decide, rfl⟩
      · split
        · exact ⟨2 + (k - 2) % 4, by omega, by omega⟩
        · exact ⟨6, by decide, rfl⟩

theorem pcOk_of_pc_s (c : Context) (k : Nat) (x : NativeState)
    (pc : x.regs._PC = c.base + offset c k) :
    (x.regs._PC = c.returnPC ∨
    ∃ j, j < 7 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memset_entry + 4 * j)) := by
  by_cases last : k = Schedule.setSteps c.n
  · left
    rw [pc]
    simp only [SetNative.offset, Schedule.nativeOffset, if_pos last]
    bv_omega
  · right
    obtain ⟨j, hj, word⟩ := setWordOffset_word c.n k
    refine ⟨j, hj, ?_⟩
    rw [pc]
    simp only [SetNative.offset, Schedule.nativeOffset, if_neg last, word, MemReloc.imageAddress]

theorem pcOk_of_env_s (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat)
    (x : NativeState) (env : EnvS c catalogue entry k x) : PcOkS c x :=
  ⟨pcOk_of_pc_s c k x env.core.v1.pc,
    CT1.Route7Word.imageWords_of_placed env.core.placed 9 7 (by decide)⟩


/-- CT1 R-a: at a non-final tick the PC is one of the routine's words. -/
theorem wordPc_of_pc_s (c : Context) (k : Nat) (hk : k ≠ Schedule.setSteps c.n) (x : NativeState)
    (pc : x.regs._PC = c.base + offset c k) :
    ∃ j, j < 7 ∧ x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memset_entry + 4 * j) := by
  obtain ⟨j, hj, word⟩ := setWordOffset_word c.n k
  refine ⟨j, hj, ?_⟩
  rw [pc]
  simp only [SetNative.offset, Schedule.nativeOffset, if_neg hk, word, MemReloc.imageAddress]

end Route7Set
#print axioms Route7Set.setWordOffset_word
#print axioms Route7Set.pcOk_of_env_s
