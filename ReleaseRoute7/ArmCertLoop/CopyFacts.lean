import ArmCertLoop.CopyContext
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft
open ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.CopyNative
open ContractDraft

theorem load_addr_zero (x : NativeState) (Rn : BitVec 5) :
    MemClass.LdrbU.addr x Rn 0#12 = x.regs.gpr[(GPRSummary.key Rn.toNat).val] := by
  change _ + 0#64 = _
  simp

theorem store_addr_zero (x : NativeState) (Rn : BitVec 5) :
    MemClass.StrbU.addr x Rn 0#12 = x.regs.gpr[(GPRSummary.key Rn.toNat).val] := by
  change _ + 0#64 = _
  simp

theorem load_facts (c : Context) (i : Nat) (room : i < c.n) (x : NativeState) (byte : BitVec 8)
    (cursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i)
    (present : x.mem[c.srcPA i]? = some byte) :
    ArmCertMemPipe.LdrbU.Facts c.spec c.config c.rows c.mapping c.consumer 0#12 1#5 x := by
  obtain ⟨pa, mapped, mmio, outside⟩ := source_mapped c i room
  have addr : MemClass.LdrbU.addr x 1#5 0#12 = c.s + BitVec.ofNat 64 i := by
    rw [load_addr_zero]; exact cursor
  have physical : c.srcPA i = pa.toNat := by simp only [Context.srcPA, mapped, Option.getD_some]
  refine ⟨pa, by rw [addr]; exact mapped, mmio, outside, ⟨byte, ?_⟩, ?_⟩
  · intro j bounded
    have : j = 0 := by omega
    subst j
    simpa [physical] using present
  · intro acc shape
    rw [addr]
    exact SpanMap.data_permitted c.footprints
      (Image.codeVAs c.base Generated.imageStart Generated.imageWords) c.mapping (rowsFootprint c.spec.imageRows).byte
      (sourceSpan c.s c.n) (by simp [Context.footprints, spans]) i room acc shape

theorem store_facts (c : Context) (i : Nat) (room : i < c.n) (x : NativeState)
    (cursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i) :
    ArmCertMemPipe.StrbU.Facts c.spec c.mapping c.consumer (DestinationPA c.mapping c.d c.n) 0#12 3#5 x := by
  obtain ⟨pa, mapped, mmio, outside⟩ := dest_mapped c i room
  have addr : MemClass.StrbU.addr x 3#5 0#12 = c.d + BitVec.ofNat 64 i := by
    rw [store_addr_zero]; exact cursor
  refine ⟨pa, by rw [addr]; exact mapped, mmio, ?_, ?_, ?_⟩
  · intro j bounded
    have : j = 0 := by omega
    subst j
    simpa using outside
  · intro j bounded
    have : j = 0 := by omega
    subst j
    exact ⟨i, room, by simpa using mapped⟩
  · intro acc shape
    rw [addr]
    exact SpanMap.data_permitted c.footprints
      (Image.codeVAs c.base Generated.imageStart Generated.imageWords) c.mapping (rowsFootprint c.spec.imageRows).byte
      (destSpan c.d c.n) (by simp [Context.footprints, spans]) i room acc shape

theorem header_source (c : Context) (entry x : NativeState) (i : Nat) (room : i < c.n)
    (present : SourcePresent c.mapping c.s c.n entry) (header : Header c entry i x) :
    ∃ byte, x.mem[c.srcPA i]? = some byte := by
  obtain ⟨pa, mapped, _, _⟩ := source_mapped c i room
  obtain ⟨byte, initial⟩ := present i room
  have physical : c.srcPA i = pa.toNat := by simp only [Context.srcPA, mapped, Option.getD_some]
  simp only [readByte, mapped, Option.bind_some] at initial
  refine ⟨byte, ?_⟩
  change Aux.memoryView x (c.srcPA i) = some byte
  rw [header.bytes.unread i (Nat.le_refl _) room]
  simpa only [Aux.memoryView, physical] using initial

#print axioms load_addr_zero
#print axioms store_addr_zero
#print axioms load_facts
#print axioms store_facts
#print axioms header_source
end ArmCertLoop.CopyNative
