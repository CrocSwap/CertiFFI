import Bridge.CruxGenGuarded.EntryClassNext
import Bridge.CruxGenGuarded.EntryBodyUmulh64Tail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryUmulhTails
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

theorem Umulh64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Umulh64.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) NativeEntryBodyAdapters.Umulh64.writes 862 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyUmulh64.native_tail real source fetched enc0 Rd Rn Rm rd rn rm profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Umulh64_tail

end ArmBridge.CruxGenGuarded.EntryUmulhTails
