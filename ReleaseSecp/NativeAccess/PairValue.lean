import NativeAccess.PairStoreRoute
import ArmCertValue.NativeBytePayload
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace NativeAccess.PairValue
open ArmBridge.Draft HeapV2StepCerts ArmCertValue
open NativeAccess.Trace NativeAccess.LdpBytes
theorem ldpLo_eq_low64 (data : BitVec 128) : ArmCertMem.LdpEval.ldpLo data = Bytes.low64 data := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [ArmCertMem.LdpEval.ldpLo,Bytes.low64,Sail.BitVec.zeroExtend,Sail.BitVec.castWidth,
    Sail.BitVec.extractLsb,BitVec.extractLsb,hi]

theorem ldpHi_eq_high64 (data : BitVec 128) : ArmCertMem.LdpEval.ldpHi data = Bytes.high64 data := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [ArmCertMem.LdpEval.ldpHi,Bytes.high64,Sail.BitVec.zeroExtend,Sail.BitVec.castWidth,
    Sail.BitVec.extractLsb,BitVec.extractLsb,hi]

theorem ldp_bytes (data : BitVec 128) (t : Nat) (ht : t < 16) :
    data.extractLsb' (8 * t) 8 =
      (if t < 8 then MemRegion.byteOf (ArmCertMem.LdpEval.ldpLo data) t
        else MemRegion.byteOf (ArmCertMem.LdpEval.ldpHi data) (t - 8)) := by
  split
  · rename_i h
    rw [← Physical.extract_byteOf,ldpLo_eq_low64,Bytes.low64_byte data t h]
  · rename_i h
    rw [← Physical.extract_byteOf,ldpHi_eq_high64,Bytes.high64_byte data (t - 8) (by omega),
      show 8 + (t - 8) = t by omega]

theorem ldp_value (view : Physical.BytePA) (regions : List Region) (x y : NativeState)
    (r : Region) (word : Nat) (Rt Rt2 : BitVec 5)
    (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2) (data : BitVec 128)
    (hg : y.regs.gpr = (ArmCertMem.LdpEval.ldpPost x Rt Rt2 data).regs.gpr)
    (memory : y.mem = x.mem)
    (payload : ∀ t, t < 16 → Physical.regionByte view x r (8 * word + t) = some (data.extractLsb' (8 * t) 8)) :
    Physical.MemVHolds view regions [.load (.x (RegBind.rk Rt)) r word,.load (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  have hne : (GPRSummary.key Rt2.toNat).val ≠ (GPRSummary.key Rt.toNat).val := by
    have k1 : ∀ n : Fin 31, (GPRSummary.key n.val).val = n.val := by decide
    rw [k1 ⟨Rt2.toNat,hRt2⟩,k1 ⟨Rt.toNat,hRt⟩]
    intro h; exact hRtt (BitVec.eq_of_toNat_eq h.symm)
  apply SplitMemory.loadPair view regions x y r word (.x (RegBind.rk Rt)) (.x (RegBind.rk Rt2))
    (ArmCertMem.LdpEval.ldpLo data) (ArmCertMem.LdpEval.ldpHi data)
  · intro t ht; rw [payload t ht,ldp_bytes data t ht]
  · change y.regs.gpr[(GPRSummary.key Rt.toNat).val] = _
    rw [hg]
    change (((x.regs.gpr.set (GPRSummary.key Rt.toNat).val _ (GPRSummary.key Rt.toNat).isLt).set (GPRSummary.key Rt2.toNat).val _ (GPRSummary.key Rt2.toNat).isLt)[(GPRSummary.key Rt.toNat).val]) = _
    rw [Vector.getElem_set_ne _ _ hne,Vector.getElem_set_self]
  · change y.regs.gpr[(GPRSummary.key Rt2.toNat).val] = _
    rw [hg]; exact Vector.getElem_set_self ..
  · exact memory

theorem ldp_one_value (view : Physical.BytePA) (regions : List Region) (x y : NativeState)
    (r : Region) (word : Nat) (mapping : BitVec 64 → Option Nat) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (lin : ∀ pa, mapping (pairAddr x Rn imm7) = some pa → ∀ i, i < 16 → view r (8 * word + i) = some (pa + i))
    (pay : PairTail.OnePay mapping Rt Rt2 imm7 Rn x y) :
    Physical.MemVHolds view regions [.load (.x (RegBind.rk Rt)) r word,.load (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  obtain ⟨pa,data,mapped,bytes,hg,_,memory,_⟩ := pay
  apply ldp_value view regions x y r word Rt Rt2 hRt hRt2 hRtt data hg memory
  intro t ht
  rw [Physical.regionByte,lin pa.toNat mapped t ht,Option.bind_some,bytes t ht]

theorem ldp_byte_value (view : Physical.BytePA) (regions : List Region) (x y : NativeState)
    (r : Region) (word : Nat) (mapping : BitVec 64 → Option Nat) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (lin : ∀ (j : Fin 16) pa, mapping (BitVec.addInt (pairAddr x Rn imm7) (j.val : Int)) = some pa →
      view r (8 * word + j.val) = some pa)
    (pay : PairTail.BytePay mapping Rt Rt2 imm7 Rn x y) :
    Physical.MemVHolds view regions [.load (.x (RegBind.rk Rt)) r word,.load (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  obtain ⟨pa,data,mapped,bytes,hg,_,memory,_⟩ := pay
  apply ldp_value view regions x y r word Rt Rt2 hRt hRt2 hRtt data hg memory
  intro t ht
  rw [Physical.regionByte,lin ⟨t,ht⟩ (pa ⟨t,ht⟩).toNat (mapped ⟨t,ht⟩),Option.bind_some]
  exact bytes ⟨t,ht⟩

#print axioms ldp_value
#print axioms ldp_one_value
#print axioms ldp_byte_value
theorem ldp_split_value (view : Physical.BytePA) (regions : List Region) (x y : NativeState)
    (r : Region) (word : Nat) (mapping : BitVec 64 → Option Nat) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (lin : ∀ (j : Fin 2) pa, mapping (PairSplit.halfAddress (pairAddr x Rn imm7) j) = some pa →
      ∀ i, i < 8 → view r (8 * word + 8 * j.val + i) = some (pa + i))
    (pay : PairTail.SplitPay mapping Rt Rt2 imm7 Rn x y) :
    Physical.MemVHolds view regions [.load (.x (RegBind.rk Rt)) r word,.load (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  obtain ⟨pa,data,mapped,bytes,hg,_,memory,_⟩ := pay
  apply ldp_value view regions x y r word Rt Rt2 hRt hRt2 hRtt data hg memory
  intro t ht
  by_cases low : t < 8
  · have hlin := lin ⟨0,by decide⟩ (pa ⟨0,by decide⟩).toNat (mapped ⟨0,by decide⟩) t low
    simp only [Nat.mul_zero,Nat.add_zero] at hlin
    rw [Physical.regionByte,hlin,Option.bind_some,bytes ⟨0,by decide⟩ t low]
    change some ((Bytes.low64 data).extractLsb' (8 * t) 8) = _
    rw [Bytes.low64_byte data t low]
  · have hi : t - 8 < 8 := by omega
    have hlin := lin ⟨1,by decide⟩ (pa ⟨1,by decide⟩).toNat (mapped ⟨1,by decide⟩) (t - 8) hi
    have eq : 8 * word + 8 * (1 : Nat) + (t - 8) = 8 * word + t := by omega
    rw [eq] at hlin
    rw [Physical.regionByte,hlin,Option.bind_some,bytes ⟨1,by decide⟩ (t - 8) hi]
    change some ((Bytes.high64 data).extractLsb' (8 * (t - 8)) 8) = _
    rw [Bytes.high64_byte data (t - 8) hi,show 8 + (t - 8) = t by omega]

#print axioms ldp_split_value
theorem stp_bytes (x : NativeState) (Rt Rt2 : BitVec 5) (t : Nat) (ht : t < 16) :
    (ArmCertMem.StpEval.stpData x Rt Rt2).extractLsb' (8 * t) 8 =
      (if t < 8 then MemRegion.byteOf (RegBind.regVal x (.x (RegBind.rk Rt))) t
        else MemRegion.byteOf (RegBind.regVal x (.x (RegBind.rk Rt2))) (t - 8)) := by
  split
  · rename_i low
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [MemRegion.byteOf_getLsbD _ _ _ hk]
    change (((x.regs.gpr[(GPRSummary.key Rt2.toNat).val]).append
      (x.regs.gpr[(GPRSummary.key Rt.toNat).val])).extractLsb' (8 * t) 8).getLsbD k = _
    rw [BitVec.getLsbD_extractLsb']
    simp only [BitVec.append,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeftZeroExtend,BitVec.getLsbD_setWidth']
    simp only [RegBind.regVal,RegBind.rk,hk,show 8 * t + k < 64 by omega,
      decide_true,Bool.true_and,Bool.not_true,Bool.false_and,Bool.false_or]
  · rename_i high
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [MemRegion.byteOf_getLsbD _ _ _ hk]
    change (((x.regs.gpr[(GPRSummary.key Rt2.toNat).val]).append
      (x.regs.gpr[(GPRSummary.key Rt.toNat).val])).extractLsb' (8 * t) 8).getLsbD k = _
    rw [BitVec.getLsbD_extractLsb']
    simp only [BitVec.append,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeftZeroExtend,BitVec.getLsbD_setWidth']
    simp only [RegBind.regVal,RegBind.rk,hk,show ¬ 8 * t + k < 64 by omega,
      decide_true,decide_false,Bool.true_and,Bool.not_false,Bool.or_false,
      BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 8 * t + k),
      show 8 * t + k - 64 = 8 * (t - 8) + k by omega]

/-- A fixed-width packet payload determines all its actual written bytes. -/
theorem writeByte_cast (c : WriteCall) (n : Nat) (hn : c.request.bytes = n) (i : Nat) (hi : i < n) :
    ArmCertValue.NativeFragments.writeByte c i =
      (Sail.BitVec.castWidth (m := n * 8) c.packet.data).extractLsb' (8 * i) 8 := by
  unfold ArmCertValue.NativeFragments.writeByte
  rw [ArmBridge.Awc.castWidth_of_eq (by omega : c.request.bytes * 8 = 8 * c.request.bytes),
    ArmBridge.Awc.castWidth_of_eq (by omega : c.request.bytes * 8 = n * 8)]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_cast]

#print axioms stp_bytes
#print axioms writeByte_cast
/-- Canonical fragment binding derived from the actual finite request list. -/
theorem bound_of_slots (view : Physical.BytePA) (r : Region) (first width : Nat)
    (calls : List WriteCall) (slots : List (Nat × Nat))
    (requests : calls.map (fun c => (c.request.offset,c.request.bytes)) = slots)
    (coverage : ∀ t : Fin width, ∃ slot ∈ slots, slot.1 ≤ t.val ∧ t.val < slot.1 + slot.2)
    (bounds : ∀ slot ∈ slots, slot.1 + slot.2 ≤ width)
    (span : ∀ c ∈ calls, ∀ i, i < c.request.bytes →
      view r (first + c.request.offset + i) = some (c.packet.ad.paddress.address.toNat + i)) :
    SplitMemory.Bound view r first width (ArmCertValue.NativeFragments.writeSegments calls) := by
  constructor
  · intro t ht
    obtain ⟨slot,member,lo,hi⟩ := coverage ⟨t,ht⟩
    rw [← requests] at member
    obtain ⟨c,hc,eq⟩ := List.mem_map.mp member
    refine ⟨ArmCertValue.NativeFragments.writeSegment c,List.mem_map.mpr ⟨c,hc,rfl⟩,?_,?_⟩
    · change c.request.offset ≤ t
      have a := congrArg Prod.fst eq
      dsimp at a
      rw [a]; exact lo
    · change t < c.request.offset + c.request.bytes
      have a := congrArg Prod.fst eq
      have b := congrArg Prod.snd eq
      dsimp at a b; rw [a,b]; exact hi
  · intro seg member
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp member
    exact bounds (c.request.offset,c.request.bytes) (by rw [← requests]; exact List.mem_map.mpr ⟨c,hc,rfl⟩)
  · intro seg member i hi
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp member
    exact span c hc i hi

#print axioms bound_of_slots
theorem stp_one_value (view : Physical.BytePA) (regions : List Region) (x y : NativeState)
    (r : Region) (word : Nat) (mapping : BitVec 64 → Option Nat) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (lin : ∀ pa, mapping (pairAddr x Rn imm7) = some pa → ∀ i, i < 16 → view r (8 * word + i) = some (pa + i))
    (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words) (injective : Physical.RegionsInjective view regions)
    (pay : PairStoreTail.OnePay mapping Rt Rt2 imm7 Rn x y) :
    Physical.MemVHolds view regions [.store (.x (RegBind.rk Rt)) r word,.store (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  obtain ⟨pa,calls,mapped,memory,⟨acc,requests⟩,payload,_,_,_⟩ := pay
  have slots : calls.map (fun c => (c.request.offset,c.request.bytes)) = [(0,16)] := by
    have h := congrArg (List.map (fun q : Access => (q.offset,q.bytes))) requests
    simpa only [List.map_map,List.map_cons,List.map_nil,Function.comp_def] using h
  have binding := bound_of_slots view r (8 * word) 16 calls [(0,16)] slots
    (by intro t; exact ⟨(0,16),by simp,by omega,by omega⟩)
    (by intro slot hs; simp only [List.mem_singleton] at hs; subst slot; decide)
    (by
      intro c hc i hi
      obtain ⟨off,size,hp,_⟩ := payload c hc
      simpa only [off,Nat.add_zero,hp] using lin pa.toNat mapped i (by omega))
  apply SplitMemory.storePair_of_writeCalls ArmCertValue.NativeFragments.writeSegment
    ArmCertValue.NativeFragments.writeByte calls view regions x y r word (.x (RegBind.rk Rt)) (.x (RegBind.rk Rt2))
    binding member fits injective
  · intro c hc i hi
    obtain ⟨off,size,hp,value⟩ := payload c hc
    change i < c.request.bytes at hi
    change ArmCertValue.NativeFragments.writeByte c i =
      (if c.request.offset + i < 8 then MemRegion.byteOf (RegBind.regVal x (.x (RegBind.rk Rt))) (c.request.offset + i)
        else MemRegion.byteOf (RegBind.regVal x (.x (RegBind.rk Rt2))) (c.request.offset + i - 8))
    rw [writeByte_cast c 16 size i (by omega),value,off,Nat.zero_add]
    exact stp_bytes x Rt Rt2 i (by omega)
  · rw [ArmCertValue.NativeFragments.writeMemory_eq] at memory
    exact memory

#print axioms stp_one_value
theorem halfValue_byte (data : BitVec 128) (j : Fin 2) (i : Nat) (hi : i < 8) :
    (PairSplit.halfValue data j).extractLsb' (8 * i) 8 = data.extractLsb' (8 * (8 * j.val + i)) 8 := by
  have cases : j.val = 0 ∨ j.val = 1 := by omega
  rcases cases with h | h
  · simp only [PairSplit.halfValue,h,ite_true,Nat.mul_zero,Nat.zero_add,Bytes.low64_byte data i hi]
  · simp only [PairSplit.halfValue,h,Nat.one_ne_zero,ite_false,Nat.mul_one,Bytes.high64_byte data i hi]

theorem stp_split_value (view : Physical.BytePA) (regions : List Region) (x y : NativeState)
    (r : Region) (word : Nat) (mapping : BitVec 64 → Option Nat) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (lin : ∀ (j : Fin 2) pa, mapping (PairSplit.halfAddress (pairAddr x Rn imm7) j) = some pa →
      ∀ i, i < 8 → view r (8 * word + 8 * j.val + i) = some (pa + i))
    (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words) (injective : Physical.RegionsInjective view regions)
    (pay : PairStoreTail.SplitPay mapping Rt Rt2 imm7 Rn x y) :
    Physical.MemVHolds view regions [.store (.x (RegBind.rk Rt)) r word,.store (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  obtain ⟨pa,calls,mapped,memory,⟨acc,requests⟩,payload,_,_,_⟩ := pay
  have slots : calls.map (fun c => (c.request.offset,c.request.bytes)) = [(0,8),(8,8)] := by
    have h := congrArg (List.map (fun q : Access => (q.offset,q.bytes))) requests
    simpa only [List.map_map,List.map_cons,List.map_nil,Function.comp_def] using h
  have binding := bound_of_slots view r (8 * word) 16 calls [(0,8),(8,8)] slots
    (by
      intro t
      by_cases h : t.val < 8
      · exact ⟨(0,8),by simp,by omega,h⟩
      · exact ⟨(8,8),by simp,by omega,by omega⟩)
    (by
      intro slot hs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl <;> decide)
    (by
      intro c hc i hi
      obtain ⟨j,off,size,hp,_⟩ := payload c hc
      simpa only [off,hp] using lin j (pa j).toNat (mapped j) i (by omega))
  apply SplitMemory.storePair_of_writeCalls ArmCertValue.NativeFragments.writeSegment
    ArmCertValue.NativeFragments.writeByte calls view regions x y r word (.x (RegBind.rk Rt)) (.x (RegBind.rk Rt2))
    binding member fits injective
  · intro c hc i hi
    obtain ⟨j,off,size,hp,value⟩ := payload c hc
    change i < c.request.bytes at hi
    change ArmCertValue.NativeFragments.writeByte c i =
      (if c.request.offset + i < 8 then MemRegion.byteOf (RegBind.regVal x (.x (RegBind.rk Rt))) (c.request.offset + i)
        else MemRegion.byteOf (RegBind.regVal x (.x (RegBind.rk Rt2))) (c.request.offset + i - 8))
    rw [writeByte_cast c 8 size i (by omega),value,halfValue_byte _ j i (by omega),off]
    exact stp_bytes x Rt Rt2 (8 * j.val + i) (by omega)
  · rw [ArmCertValue.NativeFragments.writeMemory_eq] at memory
    exact memory

#print axioms stp_split_value
theorem stp_byte_value (view : Physical.BytePA) (regions : List Region) (x y : NativeState)
    (r : Region) (word : Nat) (mapping : BitVec 64 → Option Nat) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (lin : ∀ (j : Fin 16) pa, mapping (BitVec.addInt (pairAddr x Rn imm7) (j.val : Int)) = some pa →
      view r (8 * word + j.val) = some pa)
    (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words) (injective : Physical.RegionsInjective view regions)
    (pay : PairStoreTail.BytePay mapping Rt Rt2 imm7 Rn x y) :
    Physical.MemVHolds view regions [.store (.x (RegBind.rk Rt)) r word,.store (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  obtain ⟨pa,calls,mapped,memory,⟨acc,aligned,requests⟩,payload,_,_,_⟩ := pay
  let slots := (List.range 16).map (fun j => (j,1))
  have slotsShape : (0,1) :: (List.range' 1 15).map (fun j => (j,1)) = slots := by decide
  have slotsEq : calls.map (fun c => (c.request.offset,c.request.bytes)) = slots := by
    rw [← slotsShape]
    have h := congrArg (List.map (fun q : Access => (q.offset,q.bytes))) requests
    simpa only [List.map_map,List.map_cons,List.map_nil,Function.comp_def,Loops.byteAccess,Nat.zero_add] using h
  have binding := bound_of_slots view r (8 * word) 16 calls slots slotsEq
    (by
      intro t
      exact ⟨(t.val,1),List.mem_map.mpr ⟨t.val,List.mem_range.mpr t.isLt,rfl⟩,by omega,by omega⟩)
    (by
      intro slot hs
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
      have := List.mem_range.mp hj
      dsimp; omega)
    (by
      intro c hc i hi
      obtain ⟨j,off,size,hp,_⟩ := payload c hc
      have zero : i = 0 := by omega
      subst i
      simpa only [off,hp,Nat.add_zero] using lin j (pa j).toNat (mapped j))
  apply SplitMemory.storePair_of_writeCalls ArmCertValue.NativeFragments.writeSegment
    ArmCertValue.NativeFragments.writeByte calls view regions x y r word (.x (RegBind.rk Rt)) (.x (RegBind.rk Rt2))
    binding member fits injective
  · intro c hc i hi
    obtain ⟨j,off,size,hp,value⟩ := payload c hc
    change i < c.request.bytes at hi
    have zero : i = 0 := by omega
    subst i
    change ArmCertValue.NativeFragments.writeByte c 0 =
      (if c.request.offset + 0 < 8 then MemRegion.byteOf (RegBind.regVal x (.x (RegBind.rk Rt))) (c.request.offset + 0)
        else MemRegion.byteOf (RegBind.regVal x (.x (RegBind.rk Rt2))) (c.request.offset + 0 - 8))
    rw [ArmCertValue.NativeFragments.writeByte_one c size 0 (by omega),value,off,Nat.add_zero]
    exact stp_bytes x Rt Rt2 j.val j.isLt
  · rw [ArmCertValue.NativeFragments.writeMemory_eq] at memory
    exact memory

#print axioms stp_byte_value
end NativeAccess.PairValue
