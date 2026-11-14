import Walk.S2OAOutOfRange
import Walk.S2PhysicalSizeFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2OAFrame
abbrev State := SequentialState Regs oracleChoiceSource

theorem total (address : BitVec 56) (ps : BitVec 3) (s : State)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48) :
    ∃ t : State,
      AArch64_OAOutOfRange address 0#1 ps .TGx_4KB s =
        .ok (!is_zero_subrange address 55 (S2PhysicalSizeFrame.value ps)) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases S2PhysicalSizeFrame.total ps s hPA with ⟨t, hr, hregs, hmem, hevents⟩
  have hbound := S2PhysicalSizeFrame.bounds ps
  have hlt : S2PhysicalSizeFrame.value ps < 56 := by omega
  refine ⟨t, ?_, hregs, hmem, hevents⟩
  simp [AArch64_OAOutOfRange, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, hr, hlt]

#print axioms total
end S2OAFrame
