-- GENERATED from SHA-pinned, sealed native Trace packet proofs.
-- These intermediate constructors expose the actual data equality; final
-- roots must still derive their actual ordered calls and translation facts.
import NativeAccess.Trace
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace NativeAccess.Payload
open NativeAccess.Trace
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5

theorem read_byte_packet_value (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (s : State) (pa : BitVec 56) (data : BitVec 8)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 1, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    ∃ packet : ReadPacket ⟨offset,a,1,acc,aligned,ispair⟩ s, packet.data = data := by
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
    events := by simpa only [paeq] using ev }, rfl⟩


theorem read8_natural_packet_value (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (natural : a.toNat % 8 = 0) (s : State) (pa : BitVec 56) (data : BitVec 64)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    ∃ packet : ReadPacket ⟨offset,a,8,acc,aligned,ispair⟩ s, packet.data = data := by
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
    events := by simpa only [paeq] using ev }, rfl⟩



theorem read8_within16_packet_value (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (s : State) (hlse : s.regs.FeatureImpl[111] = true) (fit : Read.Within16 a 8) (pa : BitVec 56) (data : BitVec 64)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    ∃ packet : ReadPacket ⟨offset,a,8,acc,aligned,ispair⟩ s, packet.data = data := by
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
    events := by simpa only [paeq] using ev }, rfl⟩



theorem read16_natural_packet_value (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (natural : a.toNat % 16 = 0) (s : State) (pa : BitVec 56) (data : BitVec 128)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    ∃ packet : ReadPacket ⟨offset,a,16,acc,aligned,ispair⟩ s, packet.data = data := by
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
    events := by simpa only [paeq] using ev }, rfl⟩



theorem read16_within16_packet_value (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned ispair : Bool) (s : State) (hlse : s.regs.FeatureImpl[111] = true) (fit : Read.Within16 a 16) (pa : BitVec 56) (data : BitVec 128)
    (hA : AccDR2 acc) (hM : s.regs.FeatureImpl[134] = false) (hio : NotMMIO pa)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc aligned ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      ∃ W, t1.regs = u.regs ∧ t1.mem = u.mem ∧ t1.events = u.events ++ W) :
    ∃ packet : ReadPacket ⟨offset,a,16,acc,aligned,ispair⟩ s, packet.data = data := by
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
    events := by simpa only [paeq] using ev }, rfl⟩


theorem write_within16_packet_value (r : Access) (s : State) (hn : SizeOK r.bytes)
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
    ∃ packet : WritePacket r s, packet.data = data := by
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
    events := by simpa only [paeq] using ev }, rfl⟩


theorem write_natural_packet_value (r : Access) (s : State) (hn : SizeOK r.bytes)
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
    ∃ packet : WritePacket r s, packet.data = data := by
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
    events := by simpa only [paeq] using ev }, rfl⟩


#print axioms read_byte_packet_value
#print axioms read8_natural_packet_value
#print axioms read8_within16_packet_value
#print axioms read16_natural_packet_value
#print axioms read16_within16_packet_value
#print axioms write_within16_packet_value
#print axioms write_natural_packet_value
end NativeAccess.Payload
