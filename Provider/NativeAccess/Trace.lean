import NativeAccess.Read
import NativeAccess.Store
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace NativeAccess.Trace
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5

/-- One actual MemSingle request, distinct from physical RAM fragments.
Offset is relative to the logical operand; its VA binding is proved by the
producer's geometry, rather than assumed by this record. -/
structure Access where
  offset : Nat
  va : BitVec 64
  bytes : Nat
  acc : AccessDescriptor
  aligned : Bool
  ispair : Bool

def Access.read (r : Access) : SailM (BitVec (r.bytes * 8)) :=
  AArch64_MemSingle_read__1 r.va r.bytes r.acc r.aligned r.ispair

def Access.write (r : Access) (v : BitVec (r.bytes * 8)) : SailM Unit :=
  AArch64_MemSingle_set__1 r.va r.bytes r.acc r.aligned r.ispair v

structure NormalWB (ad : AddressDescriptor) : Prop where
  normal : ad.memattrs.memtype = .MemType_Normal
  inner : ad.memattrs.inner.attrs = MemAttr_WB
  outer : ad.memattrs.outer.attrs = MemAttr_WB

theorem NormalWB.atomic_condition {ad : AddressDescriptor} (h : NormalWB ad) :
    ((ad.memattrs.memtype == MemType.MemType_Normal && ad.memattrs.inner.attrs == MemAttr_WB) &&
      ad.memattrs.outer.attrs == MemAttr_WB) = true := by
  rw [h.normal,h.inner,h.outer]
  decide

/-- Actual translation and call witnesses. No virtual/physical contiguity
across different calls, admission alignment, or future callback is stored. -/
structure ReadPacket (r : Access) (before : State) where
  data : BitVec (r.bytes * 8)
  translationInput : State
  translated : State
  after : State
  ad : AddressDescriptor
  walkEvents : Array Event
  choiceFrame : Frame before translationInput
  translation : AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int)
    translationInput = .ok ad translated
  sizeOK : SizeOK r.bytes
  ram : NotMMIO ad.paddress.address
  noFault : ad.fault.statuscode = .Fault_None
  normalWB : NormalWB ad
  translationRegs : translated.regs = before.regs
  translationMem : translated.mem = before.mem
  translationEvents : translated.events = before.events ++ walkEvents
  run : r.read before = .ok data after
  regs : after.regs = translated.regs
  mem : after.mem = translated.mem
  events : after.events = translated.events.push (.memRead ad.paddress.address.toNat r.bytes
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind r.acc) false)

structure WritePacket (r : Access) (before : State) where
  data : BitVec (r.bytes * 8)
  translationInput : State
  translated : State
  after : State
  ad : AddressDescriptor
  walkEvents : Array Event
  choiceFrame : Frame before translationInput
  translation : AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int)
    translationInput = .ok ad translated
  sizeOK : SizeOK r.bytes
  ram : NotMMIO ad.paddress.address
  noFault : ad.fault.statuscode = .Fault_None
  normalWB : NormalWB ad
  translationRegs : translated.regs = before.regs
  translationMem : translated.mem = before.mem
  translationEvents : translated.events = before.events ++ walkEvents
  run : r.write data before = .ok () after
  regs : after.regs = translated.regs
  mem : after.mem = wfold translated.mem ad.paddress.address.toNat r.bytes
    (fun j => (Sail.BitVec.castWidth (m := 8 * r.bytes) data).extractLsb' (8 * j) 8)
  events : after.events = translated.events.push (.memWrite ad.paddress.address.toNat r.bytes
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind r.acc)
    (some (Sail.BitVec.castWidth (m := 8 * r.bytes) data)) none)

theorem ReadPacket.memory {r : Access} {s : State} (p : ReadPacket r s) :
    p.after.mem = s.mem := p.mem.trans p.translationMem

theorem ReadPacket.registers {r : Access} {s : State} (p : ReadPacket r s) :
    p.after.regs = s.regs := p.regs.trans p.translationRegs

theorem WritePacket.memory {r : Access} {s : State} (p : WritePacket r s) :
    p.after.mem = wfold s.mem p.ad.paddress.address.toNat r.bytes
      (fun j => (Sail.BitVec.castWidth (m := 8 * r.bytes) p.data).extractLsb' (8 * j) 8) := by
  rw [p.mem,p.translationMem]

theorem WritePacket.registers {r : Access} {s : State} (p : WritePacket r s) :
    p.after.regs = s.regs := p.regs.trans p.translationRegs

/-- A checked concrete byte-read packet, constructed from actual translation
facts. Final callers must derive this intermediate constructor from their
current/permission/presence/walk invariant at the actual state. -/
theorem read_byte_packet (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (s : State) (pa : BitVec 56) (data : BitVec 8)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 1, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    Nonempty (ReadPacket ⟨offset,a,1,acc,aligned,ispair⟩ s) := by
  let Q := fun ad t1 => ∃ u W, Frame s u ∧
    AArch64_TranslateAddress a acc aligned ((1 : Nat) : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
    NormalWB ad ∧ t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W
  have ht : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 1, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1 := by
    intro u fu
    rcases hTA u fu with ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,W,hr,hm,he⟩
    exact ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,u,W,fu,tr,nf,paeq,⟨mt,inn,out⟩,hr,hm,he⟩
  rcases Read.single1 a aligned ispair acc s pa data hA hM Q ht hio with
    ⟨ad,t1,t,hq,post,run,ev,hr,hm⟩
  rcases hq with ⟨u,W,fu,tr,nf,paeq,wb,ur,um,ue⟩
  exact ⟨{
    data := data, translationInput := u, translated := t1, after := t, ad := ad, walkEvents := W
    choiceFrame := fu, translation := tr, sizeOK := by change SizeOK 1; unfold SizeOK; omega
    ram := by rw [paeq]; exact hio
    noFault := nf, normalWB := wb
    translationRegs := ur.trans fu.1, translationMem := um.trans fu.2.1
    translationEvents := by rw [ue,fu.2.2]
    run := run, regs := hr, mem := hm
    events := by simpa only [paeq] using ev }⟩

theorem read8_natural_packet (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (natural : a.toNat % 8 = 0) (s : State) (pa : BitVec 56) (data : BitVec 64)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    Nonempty (ReadPacket ⟨offset,a,8,acc,aligned,ispair⟩ s) := by
  let Q := fun ad t1 => ∃ u W, Frame s u ∧
    AArch64_TranslateAddress a acc aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
    NormalWB ad ∧ t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W
  have ht : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1 := by
    intro u fu
    rcases hTA u fu with ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,W,hr,hm,he⟩
    exact ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,u,W,fu,tr,nf,paeq,⟨mt,inn,out⟩,hr,hm,he⟩
  rcases Read.single8 a aligned ispair natural acc s pa data hA hM Q ht hio with
    ⟨ad,t1,t,hq,post,run,ev,hr,hm⟩
  rcases hq with ⟨u,W,fu,tr,nf,paeq,wb,ur,um,ue⟩
  exact ⟨{
    data := data, translationInput := u, translated := t1, after := t, ad := ad, walkEvents := W
    choiceFrame := fu, translation := tr, sizeOK := by change SizeOK 8; unfold SizeOK; omega
    ram := by rw [paeq]; exact hio
    noFault := nf, normalWB := wb
    translationRegs := ur.trans fu.1, translationMem := um.trans fu.2.1
    translationEvents := by rw [ue,fu.2.2]
    run := run, regs := hr, mem := hm
    events := by simpa only [paeq] using ev }⟩


theorem read8_within16_packet (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (s : State) (hlse : s.regs.FeatureImpl[111] = true) (fit : Read.Within16 a 8) (pa : BitVec 56) (data : BitVec 64)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    Nonempty (ReadPacket ⟨offset,a,8,acc,aligned,ispair⟩ s) := by
  let Q := fun ad t1 => ∃ u W, Frame s u ∧
    AArch64_TranslateAddress a acc aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
    NormalWB ad ∧ t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W
  have ht : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1 := by
    intro u fu
    rcases hTA u fu with ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,W,hr,hm,he⟩
    exact ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,u,W,fu,tr,nf,paeq,⟨mt,inn,out⟩,hr,hm,he⟩
  rcases Read.single8_within16 a aligned ispair acc s hlse fit pa data hA hM Q ht hio with
    ⟨ad,t1,t,hq,post,run,ev,hr,hm⟩
  rcases hq with ⟨u,W,fu,tr,nf,paeq,wb,ur,um,ue⟩
  exact ⟨{
    data := data, translationInput := u, translated := t1, after := t, ad := ad, walkEvents := W
    choiceFrame := fu, translation := tr, sizeOK := by change SizeOK 8; unfold SizeOK; omega
    ram := by rw [paeq]; exact hio
    noFault := nf, normalWB := wb
    translationRegs := ur.trans fu.1, translationMem := um.trans fu.2.1
    translationEvents := by rw [ue,fu.2.2]
    run := run, regs := hr, mem := hm
    events := by simpa only [paeq] using ev }⟩


theorem read16_natural_packet (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (natural : a.toNat % 16 = 0) (s : State) (pa : BitVec 56) (data : BitVec 128)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    Nonempty (ReadPacket ⟨offset,a,16,acc,aligned,ispair⟩ s) := by
  let Q := fun ad t1 => ∃ u W, Frame s u ∧
    AArch64_TranslateAddress a acc aligned ((16 : Nat) : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
    NormalWB ad ∧ t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W
  have ht : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1 := by
    intro u fu
    rcases hTA u fu with ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,W,hr,hm,he⟩
    exact ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,u,W,fu,tr,nf,paeq,⟨mt,inn,out⟩,hr,hm,he⟩
  rcases Read.single16 a aligned ispair natural acc s pa data hA hM Q ht hio with
    ⟨ad,t1,t,hq,post,run,ev,hr,hm⟩
  rcases hq with ⟨u,W,fu,tr,nf,paeq,wb,ur,um,ue⟩
  exact ⟨{
    data := data, translationInput := u, translated := t1, after := t, ad := ad, walkEvents := W
    choiceFrame := fu, translation := tr, sizeOK := by change SizeOK 16; unfold SizeOK; omega
    ram := by rw [paeq]; exact hio
    noFault := nf, normalWB := wb
    translationRegs := ur.trans fu.1, translationMem := um.trans fu.2.1
    translationEvents := by rw [ue,fu.2.2]
    run := run, regs := hr, mem := hm
    events := by simpa only [paeq] using ev }⟩


theorem read16_within16_packet (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (s : State) (hlse : s.regs.FeatureImpl[111] = true) (fit : Read.Within16 a 16) (pa : BitVec 56) (data : BitVec 128)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    Nonempty (ReadPacket ⟨offset,a,16,acc,aligned,ispair⟩ s) := by
  let Q := fun ad t1 => ∃ u W, Frame s u ∧
    AArch64_TranslateAddress a acc aligned ((16 : Nat) : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
    NormalWB ad ∧ t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W
  have ht : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1 := by
    intro u fu
    rcases hTA u fu with ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,W,hr,hm,he⟩
    exact ⟨ad,t1,tr,nf,paeq,mt,inn,out,post,bytes,u,W,fu,tr,nf,paeq,⟨mt,inn,out⟩,hr,hm,he⟩
  rcases Read.single16_within16 a aligned ispair acc s hlse fit pa data hA hM Q ht hio with
    ⟨ad,t1,t,hq,post,run,ev,hr,hm⟩
  rcases hq with ⟨u,W,fu,tr,nf,paeq,wb,ur,um,ue⟩
  exact ⟨{
    data := data, translationInput := u, translated := t1, after := t, ad := ad, walkEvents := W
    choiceFrame := fu, translation := tr, sizeOK := by change SizeOK 16; unfold SizeOK; omega
    ram := by rw [paeq]; exact hio
    noFault := nf, normalWB := wb
    translationRegs := ur.trans fu.1, translationMem := um.trans fu.2.1
    translationEvents := by rw [ue,fu.2.2]
    run := run, regs := hr, mem := hm
    events := by simpa only [paeq] using ev }⟩

/-- A checked store packet, with its precise RAM fold and actual S1 call.
The actual LSE2/within16 branch is inherited from the sealed Sail leaf proof. -/
theorem write_within16_packet (r : Access) (s : State) (hn : SizeOK r.bytes)
    (hlse : s.regs.FeatureImpl[111] = true) (fit : Read.Within16 r.va (r.bytes : Int))
    (pa : BitVec 56) (data : BitVec (r.bytes * 8)) (hA : AccDWT r.acc)
    (hT : TagOK r.acc s.regs) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK r.acc t1.regs ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    Nonempty (WritePacket r s) := by
  let Q := fun ad t1 => ∃ u W, Frame s u ∧
    AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
    NormalWB ad ∧ t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W
  have ht : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK r.acc t1.regs ∧ Q ad t1 := by
    intro u fu
    rcases hTA u fu with ⟨ad,t1,tr,nf,paeq,mt,inn,out,spe,tag,W,hr,hm,he⟩
    exact ⟨ad,t1,tr,nf,paeq,mt,inn,out,spe,tag,u,W,fu,tr,nf,paeq,⟨mt,inn,out⟩,hr,hm,he⟩
  rcases Store.store_within16 r.va r.bytes hn r.aligned r.ispair r.acc s hlse fit pa data hA hT Q ht hio with
    ⟨ad,t1,t,hq,run,ev,hr,hm⟩
  rcases hq with ⟨u,W,fu,tr,nf,paeq,wb,ur,um,ue⟩
  exact ⟨{
    data := data, translationInput := u, translated := t1, after := t, ad := ad, walkEvents := W
    choiceFrame := fu, translation := tr, sizeOK := hn
    ram := by rw [paeq]; exact hio
    noFault := nf, normalWB := wb
    translationRegs := ur.trans fu.1, translationMem := um.trans fu.2.1
    translationEvents := by rw [ue,fu.2.2]
    run := run, regs := hr
    mem := by simpa only [paeq] using hm
    events := by simpa only [paeq] using ev }⟩

theorem write_natural_packet (r : Access) (s : State) (hn : SizeOK r.bytes)
    (natural : r.va.toNat % r.bytes = 0)
    (pa : BitVec 56) (data : BitVec (r.bytes * 8)) (hA : AccDWT r.acc)
    (hT : TagOK r.acc s.regs) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK r.acc t1.regs ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    Nonempty (WritePacket r s) := by
  let Q := fun ad t1 => ∃ u W, Frame s u ∧
    AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
    NormalWB ad ∧ t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W
  have ht : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress r.va r.acc r.aligned (r.bytes : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK r.acc t1.regs ∧ Q ad t1 := by
    intro u fu
    rcases hTA u fu with ⟨ad,t1,tr,nf,paeq,mt,inn,out,spe,tag,W,hr,hm,he⟩
    exact ⟨ad,t1,tr,nf,paeq,mt,inn,out,spe,tag,u,W,fu,tr,nf,paeq,⟨mt,inn,out⟩,hr,hm,he⟩
  rcases Store.store_natural r.va r.bytes hn r.aligned r.ispair natural r.acc s pa data hA hT Q ht hio with
    ⟨ad,t1,t,hq,run,ev,hr,hm⟩
  rcases hq with ⟨u,W,fu,tr,nf,paeq,wb,ur,um,ue⟩
  exact ⟨{
    data := data, translationInput := u, translated := t1, after := t, ad := ad, walkEvents := W
    choiceFrame := fu, translation := tr, sizeOK := hn
    ram := by rw [paeq]; exact hio
    noFault := nf, normalWB := wb
    translationRegs := ur.trans fu.1, translationMem := um.trans fu.2.1
    translationEvents := by rw [ue,fu.2.2]
    run := run, regs := hr
    mem := by simpa only [paeq] using hm
    events := by simpa only [paeq] using ev }⟩

/-- Physical-event block includes the actual translation events. -/
def ReadPacket.block {r : Access} {s : State} (p : ReadPacket r s) : Array Event :=
  p.walkEvents.push (.memRead p.ad.paddress.address.toNat r.bytes (some p.ad.vaddress.toNat)
    (AccessDescriptor_to_Access_kind r.acc) false)

def WritePacket.block {r : Access} {s : State} (p : WritePacket r s) : Array Event :=
  p.walkEvents.push (.memWrite p.ad.paddress.address.toNat r.bytes (some p.ad.vaddress.toNat)
    (AccessDescriptor_to_Access_kind r.acc)
    (some (Sail.BitVec.castWidth (m := 8 * r.bytes) p.data)) none)

theorem ReadPacket.events_block {r : Access} {s : State} (p : ReadPacket r s) :
    p.after.events = s.events ++ p.block := by
  rw [p.events,p.translationEvents,Array.push_append]
  rfl

theorem WritePacket.events_block {r : Access} {s : State} (p : WritePacket r s) :
    p.after.events = s.events ++ p.block := by
  rw [p.events,p.translationEvents,Array.push_append]
  rfl

structure ReadCall where
  request : Access
  before : State
  packet : ReadPacket request before

structure WriteCall where
  request : Access
  before : State
  packet : WritePacket request before

/-- These are intermediate effect witnesses. A final root must derive the
chain from its actual Sail path; the frame bridges justify actual control
bookkeeping and do not identify complete states or supply future executions. -/
inductive ReadChain : State → List ReadCall → State → Prop where
  | nil {s t : State} (frame : Frame s t) : ReadChain s [] t
  | cons {s t : State} (c : ReadCall) {cs : List ReadCall}
      (frame : Frame s c.before) (tail : ReadChain c.packet.after cs t) : ReadChain s (c :: cs) t

inductive WriteChain : State → List WriteCall → State → Prop where
  | nil {s t : State} (frame : Frame s t) : WriteChain s [] t
  | cons {s t : State} (c : WriteCall) {cs : List WriteCall}
      (frame : Frame s c.before) (tail : WriteChain c.packet.after cs t) : WriteChain s (c :: cs) t

def readBlocks : List ReadCall → Array Event
  | [] => #[]
  | c :: cs => c.packet.block ++ readBlocks cs

def writeBlocks : List WriteCall → Array Event
  | [] => #[]
  | c :: cs => c.packet.block ++ writeBlocks cs

/-- Exact ordered physical RAM folds, allowing arbitrary overlap between
calls. No PA-contiguity or fragment-disjointness condition is imposed. -/
def writeMemory (calls : List WriteCall) (mem : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  match calls with
  | [] => mem
  | c :: cs => writeMemory cs (wfold mem c.packet.ad.paddress.address.toNat c.request.bytes
      (fun j => (Sail.BitVec.castWidth (m := 8 * c.request.bytes) c.packet.data).extractLsb' (8 * j) 8))

theorem ReadChain.memory {s t : State} {cs : List ReadCall} (h : ReadChain s cs t) :
    t.mem = s.mem := by
  induction h with
  | nil f => exact f.2.1
  | cons c f tail ih => exact ih.trans (c.packet.memory.trans f.2.1)

theorem ReadChain.registers {s t : State} {cs : List ReadCall} (h : ReadChain s cs t) :
    t.regs = s.regs := by
  induction h with
  | nil f => exact f.1
  | cons c f tail ih => exact ih.trans (c.packet.registers.trans f.1)

theorem WriteChain.memory {s t : State} {cs : List WriteCall} (h : WriteChain s cs t) :
    t.mem = writeMemory cs s.mem := by
  induction h with
  | nil f => exact f.2.1
  | cons c f tail ih =>
    rw [ih,c.packet.memory,f.2.1]
    rfl

theorem WriteChain.registers {s t : State} {cs : List WriteCall} (h : WriteChain s cs t) :
    t.regs = s.regs := by
  induction h with
  | nil f => exact f.1
  | cons c f tail ih => exact ih.trans (c.packet.registers.trans f.1)

theorem ReadChain.events {s t : State} {cs : List ReadCall} (h : ReadChain s cs t) :
    t.events = s.events ++ readBlocks cs := by
  induction h with
  | nil f => simpa only [readBlocks,Array.append_empty] using f.2.2
  | cons c f tail ih =>
    rw [ih,c.packet.events_block,f.2.2,Array.append_assoc]
    rfl

theorem WriteChain.events {s t : State} {cs : List WriteCall} (h : WriteChain s cs t) :
    t.events = s.events ++ writeBlocks cs := by
  induction h with
  | nil f => simpa only [writeBlocks,Array.append_empty] using f.2.2
  | cons c f tail ih =>
    rw [ih,c.packet.events_block,f.2.2,Array.append_assoc]
    rfl

#print axioms WriteChain.memory
#print axioms ReadChain.events
#print axioms WriteChain.events
#print axioms write_natural_packet
#print axioms read8_natural_packet
#print axioms read8_within16_packet
#print axioms read16_natural_packet
#print axioms read16_within16_packet
#print axioms read_byte_packet
#print axioms write_within16_packet
end NativeAccess.Trace
