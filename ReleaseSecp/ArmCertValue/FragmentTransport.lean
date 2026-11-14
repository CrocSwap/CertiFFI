-- Pure RAM congruence between ordered per-call bytes and the shared logical payload.
import ArmCertValue.FragmentWrites
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.SplitMemory
open HeapV2StepCerts.RegBind (St Reg regVal)

theorem wfold_congr (mem : RAM) (address width : Nat) (f g : Nat → BitVec 8)
    (same : ∀ i, i < width → f i = g i) :
    MemM1.MemWriteD1.wfold mem address width f = MemM1.MemWriteD1.wfold mem address width g := by
  apply Std.ExtHashMap.ext_getElem?
  intro pa
  rw [MemM1.MemWriteD1.wfold_get,MemM1.MemWriteD1.wfold_get]
  split
  · rename_i hit
    rw [same (pa-address) (by omega)]
  · rfl

/-- The order and original call records are retained; only physical RAM effects are projected. -/
def writeCalls {α : Type} (segment : α → Segment) (data : α → Nat → BitVec 8) : List α → RAM → RAM
  | [], mem => mem
  | call :: rest, mem => writeCalls segment data rest
      (MemM1.MemWriteD1.wfold mem (segment call).address (segment call).bytes (data call))

theorem writeCalls_eq {α : Type} (segment : α → Segment) (data : α → Nat → BitVec 8)
    (calls : List α) (bytes : Nat → BitVec 8) (mem : RAM)
    (payload : ∀ call ∈ calls, ∀ i, i < (segment call).bytes → data call i = bytes ((segment call).offset + i)) :
    writeCalls segment data calls mem = writeFragments (calls.map segment) bytes mem := by
  induction calls generalizing mem with
  | nil => rfl
  | cons call rest ih =>
    rw [writeCalls,List.map_cons,writeFragments]
    rw [wfold_congr mem (segment call).address (segment call).bytes (data call)
      (fun i => bytes ((segment call).offset + i)) (payload call (List.mem_cons_self ..))]
    exact ih _ (fun c hc => payload c (List.mem_cons_of_mem _ hc))

theorem writeCalls_payload {α : Type} (segment : α → Segment) (data : α → Nat → BitVec 8)
    (calls : List α) (bytes : Nat → BitVec 8) (mem : RAM)
    (payload : ∀ call ∈ calls, ∀ i, i < (segment call).bytes → data call i = bytes ((segment call).offset + i))
    (compatible : Compatible (calls.map segment)) :
    ∀ call ∈ calls, ∀ i, i < (segment call).bytes →
      (writeCalls segment data calls mem)[(segment call).address + i]? = some (bytes ((segment call).offset + i)) := by
  rw [writeCalls_eq segment data calls bytes mem payload]
  intro call member i hi
  exact writeFragments_payload _ bytes mem compatible (segment call) (List.mem_map.2 ⟨call,member,rfl⟩) i hi

theorem writeCalls_frame {α : Type} (segment : α → Segment) (data : α → Nat → BitVec 8)
    (calls : List α) (bytes : Nat → BitVec 8) (mem : RAM)
    (payload : ∀ call ∈ calls, ∀ i, i < (segment call).bytes → data call i = bytes ((segment call).offset + i))
    (pa : Nat) (outside : ¬ Writes (calls.map segment) pa) :
    (writeCalls segment data calls mem)[pa]? = mem[pa]? := by
  rw [writeCalls_eq segment data calls bytes mem payload]
  exact writeFragments_frame _ bytes mem pa outside

theorem storeHolds_of_writeCalls {α : Type} (segment : α → Segment) (data : α → Nat → BitVec 8)
    (calls : List α) (view : Physical.BytePA) (regions : List Region) (x y : St)
    (width : Nat) (u : VUpd) (r : Region) (first : Nat)
    (binding : Bound view r first width (calls.map segment)) (member : r ∈ regions) (fits : first + width ≤ 8 * r.words)
    (injective : Physical.RegionsInjective view regions)
    (payload : ∀ call ∈ calls, ∀ i, i < (segment call).bytes →
      data call i = ((u.eval x) >>> (8 * ((segment call).offset + i))).setWidth 8)
    (memory : y.mem = writeCalls segment data calls x.mem) :
    F.StoreHolds view regions width u r first x y := by
  apply storeHolds_of_writeFragments view regions x y width u r first _ binding member fits injective
  rw [memory]
  exact writeCalls_eq segment data calls _ x.mem payload

theorem storePair_of_writeCalls {α : Type} (segment : α → Segment) (data : α → Nat → BitVec 8)
    (calls : List α) (view : Physical.BytePA) (regions : List Region) (x y : St)
    (r : Region) (word : Nat) (rt rt2 : Reg)
    (binding : Bound view r (8 * word) 16 (calls.map segment)) (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words)
    (injective : Physical.RegionsInjective view regions)
    (payload : ∀ call ∈ calls, ∀ i, i < (segment call).bytes → data call i =
      (if (segment call).offset + i < 8 then ArmCertValue.MemRegion.byteOf (regVal x rt) ((segment call).offset + i)
        else ArmCertValue.MemRegion.byteOf (regVal x rt2) ((segment call).offset + i-8)))
    (memory : y.mem = writeCalls segment data calls x.mem) :
    Physical.MemVHolds view regions [.store rt r word,.store rt2 r (word + 1)] x y := by
  apply storePair_of_writeFragments view regions x y r word rt rt2 _ binding member fits injective
  rw [memory]
  exact writeCalls_eq segment data calls _ x.mem payload

#print axioms wfold_congr
#print axioms writeCalls_eq
#print axioms writeCalls_payload
#print axioms writeCalls_frame
#print axioms storeHolds_of_writeCalls
#print axioms storePair_of_writeCalls
end ArmCertValue.SplitMemory
