import Walk.S1EntryFrame
import GetEntry.NextGeometry
import ArmCertWalk.PhysicalRangeNat

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- The actual adjacent subsequent-entry and OA-range calls. Geometry is
source-format geometry; the physical bound is the current generalized profile. -/
theorem next_entry_range_total (params : S1TTWParams) (config : PhysicalConfig)
    (level : Nat) (va : BitVec 64) (base : FullAddress) (state : State)
    (valid : level ≤ 3) (aligned : base.address.toNat % 4096 = 0)
    (width : base.address.toNat < 2^48)
    (physical : PhysicalAt config state)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB) (ips : params.ps = config.ips)
    (bound : S1LogicalReference.entryAddress (base.address.setWidth 48) va level 9 <
      2 ^ (effectiveBits config).toNat) :
    ∃ result afterEntry afterRange,
      AArch64_TTEntryAddress (level : Int) params.d128 0#2 params.tgx params.txsz va base state =
        .ok result afterEntry ∧
      AArch64_OAOutOfRange result.address params.d128 params.ps params.tgx afterEntry =
        .ok false afterRange ∧ result.paspace = base.paspace ∧
      result.address.toNat = S1LogicalReference.entryAddress (base.address.setWidth 48) va level 9 ∧
      afterRange.regs = state.regs ∧ afterRange.mem = state.mem ∧ afterRange.events = state.events := by
  obtain ⟨afterEntry, entryCall, registers, memory, events⟩ :=
    S1EntryFrame.total (level : Int) 0#2 params.txsz va base state (by omega)
  have slot := S1EntryNextGeometry.address base va level valid aligned width
  have actualBound : (S2NextEntryFrame.address (level : Int) va base).address.toNat <
      2 ^ (effectiveBits config).toNat := by rw [slot]; exact bound
  have rangeCall := oaOutOfRange_false config _ afterEntry
    (physical.of_regs registers) actualBound
  refine ⟨S2NextEntryFrame.address (level : Int) va base, afterEntry, physicalPost afterEntry, ?_, ?_, rfl, slot, registers, memory, events⟩
  · simpa only [d128, tg] using entryCall
  · simpa only [d128, tg, ips] using rangeCall

#print axioms next_entry_range_total
end ArmCertWalk
