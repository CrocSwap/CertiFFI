import Bridge.CruxGenGuarded.EntryClassNext
import Bridge.CruxGenGuarded.EntryBodyAdcs64Tail
import Bridge.CruxGenGuarded.EntryBodyAdcs64ZRmTail
import Bridge.CruxGenGuarded.EntryBodyAddsShift64Tail
import Bridge.CruxGenGuarded.EntryBodyAndsImm0_2Tail
import Bridge.CruxGenGuarded.EntryBodySubsi64Tail
import Bridge.CruxGenGuarded.EntryBodySubsi64ZRdTail
import Bridge.CruxGenGuarded.EntryBodySubsShift64Tail
import Bridge.CruxGenGuarded.EntryBodyCsel3Tail
import Bridge.CruxGenGuarded.EntryBodyCsinc3Tail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryFlagTails
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

theorem Adcs64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adcs64.selected Rd Rn Rm) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.Adcs64.selected Rd Rn Rm) NativeEntryBodyFlag.Adcs64.writes 7 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAdcs64.native_tail real source fetched enc0 Rd Rn Rm rd rn rm noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Adcs64_tail

theorem Adcs64ZRm_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) NativeEntryBodyFlag.Adcs64ZRm.writes 7 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAdcs64ZRm.native_tail real source fetched enc0 Rd Rn rd rn noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Adcs64ZRm_tail

theorem AddsShift64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn imm6 Rm) NativeEntryBodyFlag.AddsShift64.writes 15 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAddsShift64.native_tail real source fetched enc0 Rd Rn imm6 Rm rd rn rm noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms AddsShift64_tail

theorem AndsImm0_2_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rn : BitVec 5) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) NativeEntryBodyFlag.AndsImm0_2.writes 41 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAndsImm0_2.native_tail real source fetched enc0 Rn rn noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms AndsImm0_2_tail

theorem Subsi64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) NativeEntryBodyFlag.Subsi64.writes 21 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodySubsi64.native_tail real source fetched enc0 Rd Rn imm12 rd rn noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Subsi64_tail

theorem Subsi64ZRd_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Subsi64ZRd.selected Rn imm12) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.Subsi64ZRd.selected Rn imm12) NativeEntryBodyFlag.Subsi64ZRd.writes 21 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodySubsi64ZRd.native_tail real source fetched enc0 Rn imm12 rn noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Subsi64ZRd_tail

theorem SubsShift64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) NativeEntryBodyFlag.SubsShift64.writes 17 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodySubsShift64.native_tail real source fetched enc0 Rd Rn imm6 Rm rd rn rm noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms SubsShift64_tail

theorem Csel3_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Csel3.selected Rd Rn) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.Csel3.selected Rd Rn) NativeEntryBodyFlag.Csel3.writes 187 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyCsel3.native_tail real source fetched enc0 Rd Rn rd rn noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Csel3_tail

theorem Csinc3_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (rd : Rd.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Csinc3.selected Rd) 31 12 == 879088#20) = false)
    :
    ClassTail real (NativeEntryBodyDispatch.Csinc3.selected Rd) NativeEntryBodyFlag.Csinc3.writes 188 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyCsinc3.native_tail real source fetched enc0 Rd rd noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Csinc3_tail

end ArmBridge.CruxGenGuarded.EntryFlagTails
