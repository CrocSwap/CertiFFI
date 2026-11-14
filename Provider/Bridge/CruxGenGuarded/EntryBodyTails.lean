import Bridge.CruxGenGuarded.EntryClassNext
import Bridge.CruxGenGuarded.EntryBodyAdc64Tail
import Bridge.CruxGenGuarded.EntryBodyAdc64ZRmTail
import Bridge.CruxGenGuarded.EntryBodyAddImm64Tail
import Bridge.CruxGenGuarded.EntryBodyAddSpTail
import Bridge.CruxGenGuarded.EntryBodyAddSpRestoreTail
import Bridge.CruxGenGuarded.EntryBodyMadd64Tail
import Bridge.CruxGenGuarded.EntryBodyMovz64zTail
import Bridge.CruxGenGuarded.EntryBodyOrrImm32_0Tail
import Bridge.CruxGenGuarded.EntryBodyOrrMov64Tail
import Bridge.CruxGenGuarded.EntryBodySbc64Tail
import Bridge.CruxGenGuarded.EntryBodySubSp64Tail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodyTails
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

theorem Adc64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.selected Rd Rn Rm) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Adc64.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.Adc64.selected Rd Rn Rm) NativeEntryBodyAdapters.Adc64.writes 6 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAdc64.native_tail real source fetched enc0 Rd Rn Rm rd rn rm profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Adc64_tail

theorem Adc64ZRm_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64ZRm.selected Rd Rn) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Adc64ZRm.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.Adc64ZRm.selected Rd Rn) NativeEntryBodyAdapters.Adc64ZRm.writes 6 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAdc64ZRm.native_tail real source fetched enc0 Rd Rn rd rn profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Adc64ZRm_tail

theorem AddImm64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.AddImm64.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) NativeEntryBodyAdapters.AddImm64.writes 18 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAddImm64.native_tail real source fetched enc0 Rd Rn imm12 rd rn profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms AddImm64_tail

theorem AddSp_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddSp.selected Rd imm12) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.AddSp.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.AddSp.selected Rd imm12) NativeEntryBodyAdapters.AddSp.writes 18 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAddSp.native_tail real source fetched enc0 Rd imm12 rd profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms AddSp_tail

theorem AddSpRestore_tail (real : Type) [Sail.SailReal real] (source : NativeState) (imm12 : BitVec 12) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddSpRestore.selected imm12) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.AddSpRestore.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.AddSpRestore.selected imm12) NativeEntryBodyAdapters.AddSpRestore.writes 18 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyAddSpRestore.native_tail real source fetched enc0 imm12  profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms AddSpRestore_tail

theorem Madd64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Madd64.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) NativeEntryBodyAdapters.Madd64.writes 690 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyMadd64.native_tail real source fetched enc0 Rd Rn Rm rd rn rm profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Madd64_tail

theorem Movz64z_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (imm16 : BitVec 16) (rd : Rd.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Movz64z.selected Rd imm16) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Movz64z.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.Movz64z.selected Rd imm16) NativeEntryBodyAdapters.Movz64z.writes 698 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyMovz64z.native_tail real source fetched enc0 Rd imm16 rd profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Movz64z_tail

theorem OrrImm32_0_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.OrrImm32_0.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) NativeEntryBodyAdapters.OrrImm32_0.writes 43 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyOrrImm32_0.native_tail real source fetched enc0 Rd Rn rd rn profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms OrrImm32_0_tail

theorem OrrMov64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rm : Rm.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.OrrMov64.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) NativeEntryBodyAdapters.OrrMov64.writes 55 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyOrrMov64.native_tail real source fetched enc0 Rd imm6 Rm rd rm profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms OrrMov64_tail

theorem Sbc64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Sbc64.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) NativeEntryBodyAdapters.Sbc64.writes 8 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodySbc64.native_tail real source fetched enc0 Rd Rn rd rn profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms Sbc64_tail

theorem SubSp64_tail (real : Type) [Sail.SailReal real] (source : NativeState) (imm12 : BitVec 12) (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubSp64.selected imm12) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.SubSp64.Profile source) :
    ClassTail real (NativeEntryBodyDispatch.SubSp64.selected imm12) NativeEntryBodyAdapters.SubSp64.writes 20 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodySubSp64.native_tail real source fetched enc0 imm12  profile noEret pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

#print axioms SubSp64_tail

end ArmBridge.CruxGenGuarded.EntryBodyTails
