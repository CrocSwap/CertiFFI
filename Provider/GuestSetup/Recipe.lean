import GuestSetup.Setup
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 100000
namespace GuestSetup.G3
/- E2 snapshot word; E0 TCR2 source recipe keeps all three selectors symbolic. -/
def tcr : BitVec 64 := 0x001001f5b5503510#64
def tcr2 (haft pie e0poe : Bool) : BitVec 64 :=
  (if haft then 2048#64 else 0#64) ||| (if pie then 2#64 else 0#64) |||
    (if e0poe then 4#64 else 0#64)
theorem guards (haft pie e0poe : Bool) : Guards tcr (tcr2 haft pie e0poe) := by
  cases haft <;> cases pie <;> cases e0poe <;> constructor <;> decide
theorem tg0 : _get_TCR_EL1_Type_TG0 tcr = 0#2 := by decide
theorem tg1 : _get_TCR_EL1_Type_TG1 tcr = 2#2 := by decide
theorem ips : _get_TCR_EL1_Type_IPS tcr = 5#3 := by decide
theorem txsz (vr : VARange) : GetGuestFields.Dispatch.txsz tcr vr = 16#6 := by
  cases vr <;> decide
theorem granule (vr : VARange) : GetGuestFields.Dispatch.Granule tcr vr := by
  cases vr
  · exact tg0
  · exact tg1
#print axioms guards
#print axioms txsz
end GuestSetup.G3
