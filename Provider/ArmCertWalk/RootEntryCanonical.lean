import ArmCertWalk.RootSlotProjection

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem root_entry_canonical_total (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (state : State) (current : CurrentLayoutAt layout params va state.regs)
    (level : layout.start ≤ 3) (base : FullAddress)
    (address : base.address = layout.root.setWidth 56)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB) :
    ∃ result other,
      AArch64_S1SLTTEntryAddress (layout.start : Int) params va base state = .ok result other ∧
      result.paspace = base.paspace ∧
      result.address.toNat = S1LogicalReference.entryAddress layout.root va layout.start
        (S1LogicalReference.rootBits layout.start layout.inputBits) ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨other, call, registers, memory, events⟩ :=
    root_entry_total (layout.start : Int) params va base state d128 tg
      (current_layout_entry_bounds layout params va state.regs current level)
  exact ⟨_, other, call, rfl,
    root_entry_slot_projection layout params va state.regs current level base address,
    registers, memory, events⟩

#print axioms root_entry_canonical_total

end ArmCertWalk
