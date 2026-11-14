-- Additive normalization of actual one-byte packets; no new native execution premise.
import ArmCertValue.NativeFragments
import Bridge.Awc
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCertValue.NativeFragments

theorem writeByte_one (call : NativeAccess.Trace.WriteCall) (one : call.request.bytes = 1)
    (i : Nat) (hi : i < call.request.bytes) :
    writeByte call i = Sail.BitVec.castWidth (m := 8) call.packet.data := by
  have zero : i = 0 := by omega
  subst i
  unfold writeByte
  rw [ArmBridge.Awc.castWidth_of_eq (by omega : call.request.bytes * 8 = 8 * call.request.bytes),
    ArmBridge.Awc.castWidth_of_eq (by omega : call.request.bytes * 8 = 8)]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Nat.mul_zero, BitVec.getLsbD_extractLsb', Nat.zero_add,
    BitVec.getLsbD_cast, hj, decide_true, Bool.true_and]


theorem payload_one (calls : List NativeAccess.Trace.WriteCall) (bytes : Nat → BitVec 8)
    (witness : ∀ call ∈ calls, call.request.bytes = 1 ∧
      Sail.BitVec.castWidth (m := 8) call.packet.data = bytes call.request.offset) :
    ∀ call ∈ calls, ∀ i, i < call.request.bytes → writeByte call i = bytes (call.request.offset + i) := by
  intro call member i hi
  obtain ⟨one,data⟩ := witness call member
  have zero : i = 0 := by omega
  rw [writeByte_one call one i hi, data, zero, Nat.add_zero]

theorem writeChain_fragments_one {s t : NativeAccess.Trace.State}
    {calls : List NativeAccess.Trace.WriteCall} (chain : NativeAccess.Trace.WriteChain s calls t)
    (bytes : Nat → BitVec 8)
    (witness : ∀ call ∈ calls, call.request.bytes = 1 ∧
      Sail.BitVec.castWidth (m := 8) call.packet.data = bytes call.request.offset) :
    t.mem = ArmCertValue.SplitMemory.writeFragments (writeSegments calls) bytes s.mem :=
  writeChain_fragments chain bytes (payload_one calls bytes witness)

theorem writeChain_storeHolds_one {s t : NativeAccess.Trace.State}
    {calls : List NativeAccess.Trace.WriteCall} (chain : NativeAccess.Trace.WriteChain s calls t)
    (view : Physical.BytePA) (regions : List Region) (width : Nat) (u : VUpd) (r : Region) (first : Nat)
    (binding : ArmCertValue.SplitMemory.Bound view r first width (writeSegments calls))
    (member : r ∈ regions) (fits : first + width ≤ 8 * r.words)
    (injective : Physical.RegionsInjective view regions)
    (witness : ∀ call ∈ calls, call.request.bytes = 1 ∧
      Sail.BitVec.castWidth (m := 8) call.packet.data =
        ((u.eval s) >>> (8 * call.request.offset)).setWidth 8) :
    F.StoreHolds view regions width u r first s t :=
  writeChain_storeHolds chain view regions width u r first binding member fits injective
    (payload_one calls (fun offset => ((u.eval s) >>> (8 * offset)).setWidth 8) witness)

#print axioms writeByte_one
#print axioms payload_one
#print axioms writeChain_fragments_one
#print axioms writeChain_storeHolds_one
end ArmCertValue.NativeFragments
