-- Pure RAM transport for the exact sequential wfold outputs of actual Sail store leaves.
import ArmCertValue.SplitMemory
import MemM1.MemWriteD1
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace ArmCertValue.SplitMemory
open HeapV2StepCerts.RegBind (St)
abbrev RAM := Std.ExtHashMap Nat (BitVec 8)

def writeFragments : List Segment → (Nat → BitVec 8) → RAM → RAM
  | [], _, mem => mem
  | segment :: rest, bytes, mem => writeFragments rest bytes
      (MemM1.MemWriteD1.wfold mem segment.address segment.bytes (fun i => bytes (segment.offset + i)))

/-- Overlapping physical fragments must describe the same logical byte. No disjoint-fragment restriction. -/
def Compatible (segments : List Segment) : Prop :=
  ∀ a ∈ segments, ∀ b ∈ segments, ∀ i, i < a.bytes → ∀ j, j < b.bytes →
    a.address + i=b.address + j → a.offset + i=b.offset + j

theorem Bound.compatible {view : Physical.BytePA} {region : Region} {first width : Nat}
    {segments : List Segment} (binding : Bound view region first width segments)
    (regions : List Region) (member : region ∈ regions) (fits : first + width ≤ 8*region.words)
    (injective : Physical.RegionsInjective view regions) : Compatible segments := by
  intro a ha b hb i hi j hj same
  by_cases eq : a.offset + i = b.offset + j
  · exact eq
  exfalso
  have ne := eq
  have ab := binding.bounds a ha
  have bb := binding.bounds b hb
  have ta := F.tracked_mem regions region (first + a.offset + i) member (by omega)
  have tb := F.tracked_mem regions region (first + b.offset + j) member (by omega)
  have different : (region,first + a.offset + i) ≠ (region,first + b.offset + j) := by
    intro eq
    have := congrArg Prod.snd eq
    exact ne (by dsimp at this;omega)
  exact injective _ ta _ tb different (a.address + i) (binding.span a ha i hi)
    (by rw [binding.span b hb j hj,same])

theorem writeFragments_preserves (segments : List Segment) (bytes : Nat → BitVec 8) (mem : RAM)
    (pa : Nat) (value : BitVec 8) (initial : mem[pa]? = some value)
    (same : ∀ s ∈ segments, s.address ≤ pa ∧ pa < s.address + s.bytes →
      bytes (s.offset + (pa-s.address))=value) :
    (writeFragments segments bytes mem)[pa]? = some value := by
  induction segments generalizing mem with
  | nil => exact initial
  | cons s rest ih =>
    apply ih
    · rw [MemM1.MemWriteD1.wfold_get]
      split
      · rename_i hit
        rw [same s (List.mem_cons_self ..) hit]
      · exact initial
    · intro t ht
      exact same t (List.mem_cons_of_mem _ ht)

theorem writeFragments_payload (segments : List Segment) (bytes : Nat → BitVec 8) (mem : RAM)
    (compatible : Compatible segments) :
    ∀ s ∈ segments, ∀ i, i < s.bytes →
      (writeFragments segments bytes mem)[s.address + i]? = some (bytes (s.offset + i)) := by
  induction segments generalizing mem with
  | nil => intro s hs;cases hs
  | cons head rest ih =>
    intro s hs i hi
    rw [writeFragments]
    rcases List.mem_cons.1 hs with eq | hs
    · subst s
      apply writeFragments_preserves
      · rw [MemM1.MemWriteD1.wfold_get,if_pos (by omega),show head.address + i-head.address=i by omega]
      · intro t ht hit
        congr 1
        exact compatible t (List.mem_cons_of_mem _ ht) head (List.mem_cons_self ..)
          (head.address + i-t.address) (by omega) i hi (by omega)
    · exact ih _ (fun a ha b hb => compatible a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) s hs i hi

theorem writeFragments_frame (segments : List Segment) (bytes : Nat → BitVec 8) (mem : RAM)
    (pa : Nat) (outside : ¬ Writes segments pa) :
    (writeFragments segments bytes mem)[pa]? = mem[pa]? := by
  induction segments generalizing mem with
  | nil => rfl
  | cons s rest ih =>
    rw [writeFragments,ih _ (by rintro ⟨t,ht,h⟩;exact outside ⟨t,List.mem_cons_of_mem _ ht,h⟩)]
    rw [MemM1.MemWriteD1.wfold_get,if_neg (by intro h;exact outside ⟨s,List.mem_cons_self ..,h⟩)]

theorem storeHolds_of_writeFragments (view : Physical.BytePA) (regions : List Region) (x y : St)
    (width : Nat) (u : VUpd) (r : Region) (first : Nat) (segments : List Segment)
    (binding : Bound view r first width segments) (member : r ∈ regions) (fits : first+width ≤ 8*r.words)
    (injective : Physical.RegionsInjective view regions)
    (memory : y.mem = writeFragments segments (fun t => ((u.eval x) >>> (8*t)).setWidth 8) x.mem) :
    F.StoreHolds view regions width u r first x y := by
  apply storeHolds view regions x y width u r first segments binding member fits injective
  · intro s hs i hi
    rw [memory]
    exact writeFragments_payload segments _ x.mem (binding.compatible regions member fits injective) s hs i hi
  · intro pa outside
    rw [memory]
    exact writeFragments_frame segments _ x.mem pa outside

theorem storePair_of_writeFragments (view : Physical.BytePA) (regions : List Region) (x y : St)
    (r : Region) (word : Nat) (rt rt2 : HeapV2StepCerts.RegBind.Reg) (segments : List Segment)
    (binding : Bound view r (8*word) 16 segments) (member : r ∈ regions) (fits : 8*word+16 ≤ 8*r.words)
    (injective : Physical.RegionsInjective view regions)
    (memory : y.mem = writeFragments segments
      (fun t => if t < 8 then ArmCertValue.MemRegion.byteOf (HeapV2StepCerts.RegBind.regVal x rt) t
        else ArmCertValue.MemRegion.byteOf (HeapV2StepCerts.RegBind.regVal x rt2) (t-8)) x.mem) :
    Physical.MemVHolds view regions [.store rt r word,.store rt2 r (word+1)] x y := by
  apply storePair view regions x y r word rt rt2 segments binding member fits injective
  · intro s hs i hi
    rw [memory]
    exact writeFragments_payload segments _ x.mem (binding.compatible regions member fits injective) s hs i hi
  · intro pa outside
    rw [memory]
    exact writeFragments_frame segments _ x.mem pa outside

#print axioms Bound.compatible
#print axioms writeFragments_preserves
#print axioms writeFragments_payload
#print axioms writeFragments_frame
#print axioms storeHolds_of_writeFragments
#print axioms storePair_of_writeFragments
end ArmCertValue.SplitMemory
