-- Generic byte/value/frame transport over actual physical fragments, without an alignment or contiguity assumption.
import ArmCertValue.FMemory
import ArmCertTranslate.Footprint
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace ArmCertValue.SplitMemory
open HeapV2StepCerts.RegBind (Reg St regVal)
open Physical (BytePA)

structure Segment where
  offset : Nat
  address : Nat
  bytes : Nat
  deriving DecidableEq,Repr

def Writes (segments : List Segment) (pa : Nat) : Prop :=
  ∃ segment ∈ segments, segment.address ≤ pa ∧ pa < segment.address+segment.bytes

/-- Every logical byte is covered and every actual fragment is bound to that same physical byte view. -/
structure Bound (view : BytePA) (region : Region) (first width : Nat) (segments : List Segment) : Prop where
  coverage : ∀ t, t < width → ∃ segment ∈ segments, segment.offset ≤ t ∧ t < segment.offset+segment.bytes
  bounds : ∀ segment ∈ segments, segment.offset+segment.bytes ≤ width
  span : ∀ segment ∈ segments, ∀ i, i < segment.bytes →
    view region (first+segment.offset + i) = some (segment.address + i)

def storedBytes (r : Region) (first width : Nat) : List (Region × Nat) :=
  (List.range width).map (fun t => (r,first+t))

theorem stored_mem {r q : Region} {first width j : Nat} :
    (q,j) ∈ storedBytes r first width ↔ q=r ∧ first ≤ j ∧ j < first+width := by
  constructor
  · intro h
    obtain ⟨t,ht,e⟩ := List.mem_map.1 h
    obtain ⟨rfl,eq⟩ := Prod.mk.inj e
    exact ⟨rfl,by omega,by rw [List.mem_range] at ht;omega⟩
  · rintro ⟨rfl,lo,hi⟩
    exact List.mem_map.2 ⟨j-first,List.mem_range.2 (by omega),Prod.ext rfl (by omega)⟩

theorem stored_tracked (regions : List Region) (r : Region) (first width : Nat)
    (member : r ∈ regions) (fits : first+width ≤ 8*r.words) :
    ∀ b ∈ storedBytes r first width, b ∈ Physical.trackedBytes regions := by
  intro b hb
  obtain ⟨reg,lo,hi⟩ := stored_mem.1 hb
  exact F.tracked_mem regions b.1 b.2 (reg ▸ member) (by rw [reg];omega)

theorem Bound.cover {view : BytePA} {region : Region} {first width : Nat} {segments : List Segment}
    (binding : Bound view region first width segments) :
    ∀ pa, Writes segments pa → ∃ b ∈ storedBytes region first width, view b.1 b.2 = some pa := by
  rintro pa ⟨segment,member,lo,hi⟩
  have offset : pa-segment.address < segment.bytes := by omega
  refine ⟨(region,first+segment.offset+(pa-segment.address)),?_,?_⟩
  · apply stored_mem.2
    have := binding.bounds segment member
    exact ⟨rfl,by omega,by omega⟩
  · rw [binding.span segment member (pa-segment.address) offset,show segment.address+(pa-segment.address)=pa by omega]

theorem Bound.payload {view : BytePA} {region : Region} {first width : Nat} {segments : List Segment}
    (binding : Bound view region first width segments) (s : St) (bytes : Nat → BitVec 8)
    (payload : ∀ segment ∈ segments, ∀ i, i < segment.bytes → s.mem[segment.address + i]? = some (bytes (segment.offset + i))) :
    ∀ t, t < width → Physical.regionByte view s region (first+t) = some (bytes t) := by
  intro t ht
  obtain ⟨segment,member,lo,hi⟩ := binding.coverage t ht
  have off : t-segment.offset < segment.bytes := by omega
  have index : segment.offset+(t-segment.offset)=t := by omega
  have span := binding.span segment member (t-segment.offset) off
  have out := payload segment member (t-segment.offset) off
  rw [index] at out
  unfold Physical.regionByte
  rw [show first+t=first+segment.offset+(t-segment.offset) by omega,span,Option.bind_some]
  exact out

/-- SSA source-byte agreement supplies every read fragment's actual RAM presence, including page crossings. -/
theorem read_present {view : BytePA} {region : Region} {first width : Nat} {segments : List Segment}
    (binding : Bound view region first width segments) {vals : List (BitVec 64)} {σ : Sym} {x : St}
    (agrees : Physical.Agrees view vals σ x)
    (covered : ∀ t, t < width → ∃ i k, σ.memB region (first+t) = some (i,k)) :
    ∀ segment ∈ segments, ∀ j, j < segment.bytes → (x.mem[segment.address + j]?).isSome := by
  intro segment member j hj
  obtain ⟨i,k,tracked⟩ := covered (segment.offset + j) (by have := binding.bounds segment member;omega)
  exact Physical.present_of_agrees agrees tracked
    (by simpa only [Nat.add_assoc] using binding.span segment member j hj)

/-- A span store's semantic payload and physical frame need no whole-access PA interval. -/
theorem storeHolds (view : BytePA) (regions : List Region) (x y : St)
    (width : Nat) (u : VUpd) (r : Region) (first : Nat) (segments : List Segment)
    (binding : Bound view r first width segments) (member : r ∈ regions) (fits : first+width ≤ 8*r.words)
    (injective : Physical.RegionsInjective view regions)
    (payload : ∀ segment ∈ segments, ∀ i, i < segment.bytes →
      y.mem[segment.address + i]? = some (((u.eval x) >>> (8*(segment.offset + i))).setWidth 8))
    (frame : ∀ pa, ¬ Writes segments pa → y.mem[pa]? = x.mem[pa]?) :
    F.StoreHolds view regions width u r first x y := by
  refine ⟨binding.payload y _ payload,?_⟩
  intro q hq j hj outside
  apply Physical.frame_of_cover view regions x y (Writes segments) frame (storedBytes r first width)
    binding.cover injective (stored_tracked regions r first width member fits) q j (F.tracked_mem regions q j hq hj)
  intro hit
  exact outside (stored_mem.1 hit)

/-- Build legacy memory effects from their payload clauses and a byte-level frame over arbitrary write fragments. -/
theorem memV_of_byteFrames (view : BytePA) (regions : List Region) (x y : St) (effects : List MemEff)
    (payload : ∀ effect ∈ effects, Physical.MemVHolds view [] [effect] x y)
    (frame : ∀ r ∈ regions, ∀ j, j < 8*r.words → Physical.ByteFree effects r j →
      Physical.regionByte view y r j = Physical.regionByte view x r j) :
    Physical.MemVHolds view regions effects x y := by
  refine ⟨fun e he => (payload e he).1 e (List.mem_singleton_self e),?_,?_⟩
  · intro r hr w hw h1 h2 h3
    apply Physical.regionWord_congr view x y r w
    intro k hk
    apply frame r hr (8*w+k) (by omega)
    refine ⟨?_,?_,?_⟩
    · intro rt hit
      exact h2 rt (8*w+k) hit (by omega)
    · intro rt hit
      rw [show (8*w+k)/8=w by omega] at hit
      exact h1 rt hit
    · intro rt first hit
      rcases h3 rt first hit with lo | hi <;> omega
  · intro r hr j hj h1 h2 h3
    exact frame r hr j hj ⟨h1,h2,h3⟩

/-- Pair-load value assembly from the actual sixteen byte observations. Alignment is a machine-path obligation. -/
theorem loadPair (view : BytePA) (regions : List Region) (x y : St)
    (r : Region) (word : Nat) (lo hi : Reg) (low high : BitVec 64)
    (payload : ∀ t, t < 16 → Physical.regionByte view x r (8*word+t) =
      some (if t < 8 then ArmCertValue.MemRegion.byteOf low t else ArmCertValue.MemRegion.byteOf high (t-8)))
    (regLo : regVal y lo = low) (regHi : regVal y hi = high) (memory : y.mem=x.mem) :
    Physical.MemVHolds view regions [.load lo r word,.load hi r (word+1)] x y := by
  apply Physical.memV_loads view regions x y _ memory
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · refine ⟨lo,r,word,rfl,?_⟩
    rw [regLo]
    apply Physical.regionWord_of_bytes view x r word low
    intro t ht
    simpa only [if_pos ht] using payload t (by omega)
  · refine ⟨hi,r,word+1,rfl,?_⟩
    rw [regHi]
    apply Physical.regionWord_of_bytes view x r (word+1) high
    intro t ht
    have out := payload (8+t) (by omega)
    rw [if_neg (by omega),show 8+t-8=t by omega] at out
    simpa only [show 8*(word+1)+t=8*word+(8+t) by omega] using out

/-- Pair-store values and frames from actual fragments, including discontiguous physical page outputs. -/
theorem storePair (view : BytePA) (regions : List Region) (x y : St) (r : Region) (word : Nat)
    (rt rt2 : Reg) (segments : List Segment) (binding : Bound view r (8*word) 16 segments)
    (member : r ∈ regions) (fits : 8*word+16 ≤ 8*r.words) (injective : Physical.RegionsInjective view regions)
    (payload : ∀ segment ∈ segments, ∀ i, i < segment.bytes → y.mem[segment.address + i]? =
      some (if segment.offset + i < 8 then ArmCertValue.MemRegion.byteOf (regVal x rt) (segment.offset + i)
        else ArmCertValue.MemRegion.byteOf (regVal x rt2) (segment.offset + i-8)))
    (frame : ∀ pa, ¬ Writes segments pa → y.mem[pa]? = x.mem[pa]?) :
    Physical.MemVHolds view regions [.store rt r word,.store rt2 r (word+1)] x y := by
  have bytes := binding.payload y (fun t => if t < 8 then ArmCertValue.MemRegion.byteOf (regVal x rt) t else ArmCertValue.MemRegion.byteOf (regVal x rt2) (t-8)) payload
  have low : Physical.regionWord view y r word = some (regVal x rt) := by
    apply Physical.regionWord_of_bytes
    intro t ht
    simpa only [if_pos ht] using bytes t (by omega)
  have high : Physical.regionWord view y r (word+1) = some (regVal x rt2) := by
    apply Physical.regionWord_of_bytes
    intro t ht
    have out := bytes (8+t) (by omega)
    rw [if_neg (by omega),show 8+t-8=t by omega] at out
    simpa only [show 8*(word+1)+t=8*word+(8+t) by omega] using out
  apply memV_of_byteFrames view regions x y _
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · refine ⟨?_,?_,?_⟩
      · intro e he
        have eq := List.mem_singleton.1 he
        subst e
        exact low
      · intro q hq;cases hq
      · intro q hq;cases hq
    · refine ⟨?_,?_,?_⟩
      · intro e he
        have eq := List.mem_singleton.1 he
        subst e
        exact high
      · intro q hq;cases hq
      · intro q hq;cases hq
  · intro q hq j hj free
    apply Physical.frame_of_cover view regions x y (Writes segments) frame (storedBytes r (8*word) 16)
      binding.cover injective (stored_tracked regions r (8*word) 16 member fits) q j (F.tracked_mem regions q j hq hj)
    intro hit
    obtain ⟨reg,lower,upper⟩ := stored_mem.1 hit
    subst q
    by_cases small : j < 8*word+8
    · apply free.2.1 rt
      rw [show j/8=word by omega]
      exact List.mem_cons_self ..
    · apply free.2.1 rt2
      rw [show j/8=word+1 by omega]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

#print axioms Bound.payload
#print axioms read_present
#print axioms storeHolds
#print axioms memV_of_byteFrames
#print axioms loadPair
#print axioms storePair
end ArmCertValue.SplitMemory
