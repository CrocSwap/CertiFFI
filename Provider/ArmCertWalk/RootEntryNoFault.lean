import ArmCertWalk.RootEntryCanonical
import ArmCertWalk.PhysicalRangeNat

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

/-- The two adjacent actual source calls at the root. The no-range-fault
result follows from CURRENT layout/profile data and the finite slot bound. -/
theorem root_entry_range_total (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (config : PhysicalConfig) (va : BitVec 64) (state : State)
    (current : CurrentLayoutAt layout params va state.regs)
    (physical : PhysicalAt config state) (level : layout.start ≤ 3) (base : FullAddress)
    (address : base.address = layout.root.setWidth 56)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB) (ips : params.ps = config.ips)
    (bound : S1LogicalReference.entryAddress layout.root va layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) < 2 ^ (effectiveBits config).toNat) :
    ∃ result afterEntry afterRange,
      AArch64_S1SLTTEntryAddress (layout.start : Int) params va base state = .ok result afterEntry ∧
      AArch64_OAOutOfRange result.address params.d128 params.ps params.tgx afterEntry =
        .ok false afterRange ∧ result.paspace = base.paspace ∧
      result.address.toNat = S1LogicalReference.entryAddress layout.root va layout.start
        (S1LogicalReference.rootBits layout.start layout.inputBits) ∧
      afterRange.regs = state.regs ∧ afterRange.mem = state.mem ∧ afterRange.events = state.events := by
  obtain ⟨result, afterEntry, entryCall, space, slot, registers, memory, events⟩ :=
    root_entry_canonical_total layout params va state current level base address d128 tg
  have actualBound : result.address.toNat < 2 ^ (effectiveBits config).toNat := by
    rw [slot]
    exact bound
  have rangeCall := oaOutOfRange_false config result.address afterEntry
    (physical.of_regs registers) actualBound
  refine ⟨result, afterEntry, physicalPost afterEntry, entryCall, ?_, space, slot,
    registers, memory, events⟩
  simpa only [d128, tg, ips] using rangeCall

#print axioms root_entry_range_total

end ArmCertWalk
