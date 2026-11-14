-- Physical byte-span adapter for actual Sail write payloads.
import ArmCertValue.F
import ArmCertValue.PhysicalMemory
import MemM1.MemWriteD1
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.F
open HeapV2StepCerts.RegBind (St)
open Physical (BytePA)

theorem tracked_mem (regions : List Region) (r : Region) (j : Nat)
    (hr : r ∈ regions) (hj : j < 8 * r.words) : (r,j) ∈ Physical.trackedBytes regions := by
  apply List.mem_flatMap.2
  refine ⟨r,hr,List.mem_map.2 ?_⟩
  exact ⟨j,List.mem_range.2 hj,rfl⟩

/-- A real write payload establishes the span-store relation, including the physical frame. -/
theorem storeHolds_of_wfold (bytePA : BytePA) (regions : List Region) (x y : St)
    (width : Nat) (u : VUpd) (r : Region) (j pa : Nat) (value : BitVec (8 * width))
    (member : r ∈ regions) (fits : j + width ≤ 8 * r.words)
    (view : ∀ t, t < width → bytePA r (j+t) = some (pa+t))
    (inj : Physical.RegionsInjective bytePA regions)
    (bytes : ∀ t, t < width → value.extractLsb' (8*t) 8 = ((u.eval x) >>> (8*t)).setWidth 8)
    (write : y.mem = MemM1.MemWriteD1.wfold x.mem pa width (fun t => value.extractLsb' (8*t) 8)) :
    StoreHolds bytePA regions width u r j x y := by
  refine ⟨?_,?_⟩
  · intro t ht
    rw [Physical.regionByte, view t ht, Option.bind_some, write, MemM1.MemWriteD1.wfold_get,
      if_pos (by omega), show pa+t-pa=t by omega, bytes t ht]
  · intro q hq k hk outside
    unfold Physical.regionByte
    cases loc : bytePA q k with
    | none => rfl
    | some address =>
      simp only [Option.bind_some]
      have miss : ¬ (pa ≤ address ∧ address < pa+width) := by
        intro interval
        have off : address-pa < width := by omega
        have neq : (q,k) ≠ (r,j+(address-pa)) := by
          intro e
          have eq := Prod.mk.inj e
          exact outside ⟨eq.1, by omega, by omega⟩
        have distinct := inj (q,k) (tracked_mem regions q k hq hk)
          (r,j+(address-pa)) (tracked_mem regions r _ member (by omega)) neq address loc
        apply distinct
        change bytePA r (j+(address-pa)) = some address
        rw [view (address-pa) off, show pa+(address-pa)=address by omega]
      rw [write, MemM1.MemWriteD1.wfold_get, if_neg miss]

#print axioms storeHolds_of_wfold
end ArmCertValue.F
