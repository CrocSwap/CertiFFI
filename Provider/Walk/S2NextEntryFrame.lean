import Walk.S2NextEntryAddress
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2NextEntryFrame
abbrev State := SequentialState Regs oracleChoiceSource

def address (level : Int) (ia : BitVec 64) (table : FullAddress) : FullAddress :=
  let lsb : Int := (3 - level) * 9 + 12
  let msb : Int := lsb + 8
  {table with address := table.address |||
    Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb ia (Sail.Int.toNatChecked msb)
      (Sail.Int.toNatChecked lsb)) +++ (0#3)) 56}
def Effect (level : Int) (ia : BitVec 64) (table : FullAddress) (s : State) :
    EStateM.Result (Sail.Error exception) State FullAddress → Prop
  | .ok a t => a = address level ia table ∧ t.regs = s.regs ∧ t.mem = s.mem
  | .error _ _ => False

theorem effect (level : Int) (skl : BitVec 2) (txsz : BitVec 6)
    (ia : BitVec 64) (table : FullAddress) (s : State)
    (hlevel : 0 ≤ level ∧ level ≤ 3) :
    Effect level ia table s
      (AArch64_TTEntryAddress level 0#1 skl .TGx_4KB txsz ia table s) := by
  rw [S2NextEntryAddress.complete]
  have hcases : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    delta S2NextEntryAddress.native <;> simp [Effect, address] <;> rfl
theorem total (level : Int) (skl : BitVec 2) (txsz : BitVec 6)
    (ia : BitVec 64) (table : FullAddress) (s : State)
    (hlevel : 0 ≤ level ∧ level ≤ 3) :
    ∃ t : State,
      AArch64_TTEntryAddress level 0#1 skl .TGx_4KB txsz ia table s =
        .ok (address level ia table) t ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  have he := effect level skl txsz ia table s hlevel
  cases hr : AArch64_TTEntryAddress level 0#1 skl .TGx_4KB txsz ia table s with
  | error err t => simp only [hr, Effect] at he
  | ok a t =>
    simp only [hr, Effect] at he
    rcases he with ⟨ha, hregs, hmem⟩
    subst a
    exact ⟨t, rfl, hregs, hmem⟩
#print axioms total

#print axioms effect
end S2NextEntryFrame
