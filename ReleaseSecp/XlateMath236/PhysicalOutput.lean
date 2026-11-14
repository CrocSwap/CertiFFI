import SecpMath.CoreSub
import ArmCertValue.Physical
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace XlateMath236.PhysicalOutput
open ArmCertValue SecpMath

def wordBytes (word : BitVec 64) : List (BitVec 8) :=
  (List.range 8).map fun k => (word >>> (8*k)).setWidth 8

def limbBytes (words : LimbWords) : List (BitVec 8) :=
  wordBytes words.w0 ++ wordBytes words.w1 ++ wordBytes words.w2 ++ wordBytes words.w3

def symbolicBytes (values : List (BitVec 64)) (sym : Sym) (region : Region) : List (Option (BitVec 8)) :=
  (List.range 32).map fun j =>
    (sym.memB region j).map fun q => ((values.getD q.1 0) >>> (8*q.2)).setWidth 8

def physicalBytes (view : Physical.BytePA) (state : HeapV2StepCerts.RegBind.St)
    (region : Region) : List (Option (BitVec 8)) :=
  (List.range 32).map (Physical.regionByte view state region)

/-- Storage adapter only. A whole-program proof must establish `agrees` for its
actual final Sail state; this state relation is not an entry/deployment premise. -/
theorem physical_bytes_of_agrees (values : List (BitVec 64)) (sym : Sym) (region : Region)
    (view : Physical.BytePA) (state : HeapV2StepCerts.RegBind.St) (ids : List (Nat × Nat))
    (agrees : Physical.Agrees view values sym state)
    (tracked : (List.range 32).map (sym.memB region) = ids.map some) :
    physicalBytes view state region = symbolicBytes values sym region := by
  apply List.map_congr_left
  intro j member
  have seen : sym.memB region j ∈ ids.map some := by
    rw [← tracked]
    exact List.mem_map.mpr ⟨j, member, rfl⟩
  obtain ⟨⟨i,k⟩, _, same⟩ := List.mem_map.mp seen
  have slot : sym.memB region j = some (i,k) := same.symm
  rw [slot]
  exact agrees.2.2 region j i k slot

theorem bytes_of_ids (values : List (BitVec 64)) (sym : Sym) (region : Region)
    (ids : List (Nat × Nat))
    (tracked : (List.range 32).map (sym.memB region) = ids.map some) :
    symbolicBytes values sym region =
      ids.map (fun q => some (((values.getD q.1 0) >>> (8*q.2)).setWidth 8)) := by
  let decode : Option (Nat × Nat) → Option (BitVec 8) := fun q =>
    q.map fun pair => ((values.getD pair.1 0) >>> (8*pair.2)).setWidth 8
  have h := congrArg (List.map decode) tracked
  simpa only [symbolicBytes, List.map_map, Function.comp_def, decode, Option.map_some] using h

#print axioms physical_bytes_of_agrees
#print axioms bytes_of_ids
end XlateMath236.PhysicalOutput
