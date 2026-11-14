import Bridge.CruxGenGuarded.EntryClassNext
import Bridge.CruxGenGuarded.EntryBodySbcs64Tail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntrySbcsTails
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

theorem Sbcs64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) NativeEntryBodyFlag.Sbcs64.writes 9 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodySbcs64.native_tail real source fetched enc0 Rd Rn rd rn noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Sbcs64_tail

end ArmBridge.CruxGenGuarded.EntrySbcsTails
