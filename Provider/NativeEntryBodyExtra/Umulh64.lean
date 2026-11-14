import Bridge.CruxIUmulh1
import Sail.AbstractRealRat
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyExtra.Umulh64
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- Core 3d5c: the Umulh64 tail needs BTypeNext (and mem/events) on the SAME actual
successor as the sealed trio (entry-body-trio-d145-umulh). Taken from Core's
canonical, already-gated SDK frame ArmBridge.CruxIUmulh1.madd_frame (Ra literal 31;
the Rat instance is irrelevant to the statement). -/
theorem frame (s : NativeState) (Rd Rn Rm : BitVec 5) :
    ∃ t, (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) s = .ok () t ∧
      t.regs.BTypeNext = s.regs.BTypeNext ∧ t.mem = s.mem ∧ t.events = s.events := by
  obtain ⟨ok, h⟩ := ArmBridge.CruxIUmulh1.madd_frame Rat Rd Rn (31#5) Rm s
  refine ⟨_, ok, ?_, ?_, ?_⟩
  · simpa [ArmBridge.CruxIUmulh1.maddF] using congrArg (fun x => x.2.2.2.1) h
  · simpa [ArmBridge.CruxIUmulh1.maddF] using congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) h
  · simpa [ArmBridge.CruxIUmulh1.maddF] using congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h

#print axioms frame
end NativeEntryBodyExtra.Umulh64
