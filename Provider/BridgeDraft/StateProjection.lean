import ArmFull.Defs

/-! BridgeDraft.StateProjection, Sail-only part (a design decision (b), d194). The LNSym projection
(`project`, `FormProfileTOTAL`, `PreservesAdmission`, project_* lemmas) moved to the QUARANTINED module
BridgeDraft.StateProjectionLNSym, which no release-path module may import. -/

namespace ArmBridge.Draft
open Sail.ConcurrencyInterfaceV1

abbrev NativeState := SequentialState ArmFull.Regs oracleChoiceSource

/-- Exact raw values for the current LNSym SYS API and LN12 branch controls.
Other selectors have no projected semantics in this draft. The admission
contract must prohibit observing those zero-filled entries. -/
def systemRegisters (r : ArmFull.Regs) (selector : BitVec 16) : BitVec 64 :=
  match selector.toNat with
  | 0xde82 => ArmFull.Register.TPIDR_EL0.get r
  | 0xde83 => ArmFull.Register.TPIDRRO_EL0.get r
  | 0xd807 => ArmFull.Register.DCZID_EL0.get r
  | 0xc000 => ArmFull.Register.MIDR_EL1.get r
  | 0xc031 => ArmFull.Register.ID_AA64ISAR1_EL1.get r
  | 0xc032 => ArmFull.Register.ID_AA64ISAR2_EL1.get r
  | 0xc039 => ArmFull.Register.ID_AA64MMFR1_EL1.get r
  | 0xc102 => ArmFull.Register.TCR_EL1.get r
  | 0xe102 => ArmFull.Register.TCR_EL2.get r
  | 0xe088 => ArmFull.Register.HCR_EL2.get r
  | _ => 0#64

end ArmBridge.Draft
