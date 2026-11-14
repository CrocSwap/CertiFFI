import Walk.S2PhysicalSize
import Walk.S2Frame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2PhysicalSizeFrame
abbrev State := SequentialState Regs oracleChoiceSource
def value (ps : BitVec 3) : Int :=
  if ps = 0#3 then 32 else
  if ps = 1#3 then 36 else
  if ps = 2#3 then 40 else
  if ps = 3#3 then 42 else
  if ps = 4#3 then 44 else
  48
def Effect (ps : BitVec 3) (s : State) : S2PhysicalSize.Result → Prop
  | .ok n t => n = value ps ∧ t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events
  | .error _ _ => False
theorem normal0 (s : State) : Effect 0#3 s (S2PhysicalSize.native0 48 s) := by
  delta S2PhysicalSize.native0
  simp [Effect, value, show min (52 : Int) 48 = 48 by decide] <;> decide
theorem normal1 (s : State) : Effect 1#3 s (S2PhysicalSize.native1 48 s) := by
  delta S2PhysicalSize.native1
  simp [Effect, value, show min (52 : Int) 48 = 48 by decide] <;> decide
theorem normal2 (s : State) : Effect 2#3 s (S2PhysicalSize.native2 48 s) := by
  delta S2PhysicalSize.native2
  simp [Effect, value, show min (52 : Int) 48 = 48 by decide] <;> decide
theorem normal3 (s : State) : Effect 3#3 s (S2PhysicalSize.native3 48 s) := by
  delta S2PhysicalSize.native3
  simp [Effect, value, show min (52 : Int) 48 = 48 by decide] <;> decide
theorem normal4 (s : State) : Effect 4#3 s (S2PhysicalSize.native4 48 s) := by
  delta S2PhysicalSize.native4
  simp [Effect, value, show min (52 : Int) 48 = 48 by decide] <;> decide
theorem normal5 (s : State) : Effect 5#3 s (S2PhysicalSize.native5 48 s) := by
  delta S2PhysicalSize.native5
  simp [Effect, value, show min (52 : Int) 48 = 48 by decide] <;> decide
theorem normal6 (s : State) : Effect 6#3 s (S2PhysicalSize.native6 48 s) := by
  delta S2PhysicalSize.native6
  simp [Effect, value, show min (52 : Int) 48 = 48 by decide] <;> decide
theorem normal7 (s : State) : Effect 7#3 s (S2PhysicalSize.native7 48 s) := by
  delta S2PhysicalSize.native7
  simp [Effect, value, show min (52 : Int) 48 = 48 by decide] <;> decide
theorem effect (ps : BitVec 3) (s : State)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48) :
    Effect ps s (AArch64_PhysicalAddressSize 0#1 ps .TGx_4KB s) := by
  rw [S2PhysicalSize.complete 48 ps s hPA]
  by_cases h0 : ps = 0#3
  · simpa [S2PhysicalSize.native, h0] using normal0 s
  by_cases h1 : ps = 1#3
  · simpa [S2PhysicalSize.native, h1] using normal1 s
  by_cases h2 : ps = 2#3
  · simpa [S2PhysicalSize.native, h2] using normal2 s
  by_cases h3 : ps = 3#3
  · simpa [S2PhysicalSize.native, h3] using normal3 s
  by_cases h4 : ps = 4#3
  · simpa [S2PhysicalSize.native, h4] using normal4 s
  by_cases h5 : ps = 5#3
  · simpa [S2PhysicalSize.native, h5] using normal5 s
  by_cases h6 : ps = 6#3
  · simpa [S2PhysicalSize.native, h6] using normal6 s
  have h7 : ps = 7#3 := by
    have hb := ps.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  simpa [S2PhysicalSize.native, h7] using normal7 s

theorem total (ps : BitVec 3) (s : State)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48) :
    ∃ t : State, AArch64_PhysicalAddressSize 0#1 ps .TGx_4KB s = .ok (value ps) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  have h := effect ps s hPA
  cases hr : AArch64_PhysicalAddressSize 0#1 ps .TGx_4KB s with
  | error err t => simp only [hr, Effect] at h
  | ok n t =>
    simp only [hr, Effect] at h
    rcases h with ⟨rfl, hregs, hmem, hevents⟩
    exact ⟨t, rfl, hregs, hmem, hevents⟩

theorem bounds (ps : BitVec 3) : 32 ≤ value ps ∧ value ps ≤ 48 := by
  unfold value
  repeat' first | split | omega
#print axioms total
#print axioms bounds
end S2PhysicalSizeFrame
