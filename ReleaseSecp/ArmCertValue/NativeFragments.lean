-- Canonical physical projections from actual native call witnesses; no query/descriptor rewriting.
import ArmCertValue.FragmentTransport
import NativeAccess.Trace
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.NativeFragments
open HeapV2StepCerts.RegBind (St Reg regVal)

def writeSegment (call : NativeAccess.Trace.WriteCall) : ArmCertValue.SplitMemory.Segment :=
  ⟨call.request.offset,call.packet.ad.paddress.address.toNat,call.request.bytes⟩

def readSegment (call : NativeAccess.Trace.ReadCall) : ArmCertValue.SplitMemory.Segment :=
  ⟨call.request.offset,call.packet.ad.paddress.address.toNat,call.request.bytes⟩

def writeSegments (calls : List NativeAccess.Trace.WriteCall) : List ArmCertValue.SplitMemory.Segment := calls.map writeSegment
def readSegments (calls : List NativeAccess.Trace.ReadCall) : List ArmCertValue.SplitMemory.Segment := calls.map readSegment

def writeByte (call : NativeAccess.Trace.WriteCall) (j : Nat) : BitVec 8 :=
  (Sail.BitVec.castWidth (m := 8 * call.request.bytes) call.packet.data).extractLsb' (8 * j) 8

theorem writeMemory_eq (calls : List NativeAccess.Trace.WriteCall) (mem : ArmCertValue.SplitMemory.RAM) :
    NativeAccess.Trace.writeMemory calls mem = ArmCertValue.SplitMemory.writeCalls writeSegment writeByte calls mem := by
  induction calls generalizing mem with
  | nil => rfl
  | cons call rest ih =>
    rw [NativeAccess.Trace.writeMemory,ArmCertValue.SplitMemory.writeCalls]
    exact ih _

/-- An outside-write frame needs no logical payload, overlap compatibility or instruction success oracle. -/
theorem writeCalls_frame_raw {α : Type} (segment : α → ArmCertValue.SplitMemory.Segment) (data : α → Nat → BitVec 8)
    (calls : List α) (mem : ArmCertValue.SplitMemory.RAM) (pa : Nat) (outside : ¬ ArmCertValue.SplitMemory.Writes (calls.map segment) pa) :
    (ArmCertValue.SplitMemory.writeCalls segment data calls mem)[pa]? = mem[pa]? := by
  induction calls generalizing mem with
  | nil => rfl
  | cons call rest ih =>
    rw [ArmCertValue.SplitMemory.writeCalls,ih _ (by
      rintro ⟨s,member,hit⟩
      exact outside ⟨s,List.mem_cons_of_mem _ member,hit⟩)]
    rw [MemM1.MemWriteD1.wfold_get,if_neg (by
      intro hit
      exact outside ⟨segment call,List.mem_cons_self ..,hit⟩)]

theorem writeChain_frame {s t : NativeAccess.Trace.State} {calls : List NativeAccess.Trace.WriteCall} (chain : NativeAccess.Trace.WriteChain s calls t) :
    ∀ pa, ¬ ArmCertValue.SplitMemory.Writes (writeSegments calls) pa → t.mem[pa]? = s.mem[pa]? := by
  intro pa outside
  rw [chain.memory,writeMemory_eq]
  exact writeCalls_frame_raw writeSegment writeByte calls s.mem pa outside

theorem writeChain_fragments {s t : NativeAccess.Trace.State} {calls : List NativeAccess.Trace.WriteCall} (chain : NativeAccess.Trace.WriteChain s calls t)
    (bytes : Nat → BitVec 8)
    (payload : ∀ call ∈ calls, ∀ i, i < call.request.bytes → writeByte call i = bytes (call.request.offset + i)) :
    t.mem = ArmCertValue.SplitMemory.writeFragments (writeSegments calls) bytes s.mem := by
  rw [chain.memory,writeMemory_eq]
  exact ArmCertValue.SplitMemory.writeCalls_eq writeSegment writeByte calls bytes s.mem payload

theorem writeChain_storeHolds {s t : NativeAccess.Trace.State} {calls : List NativeAccess.Trace.WriteCall} (chain : NativeAccess.Trace.WriteChain s calls t)
    (view : Physical.BytePA) (regions : List Region) (width : Nat) (u : VUpd) (r : Region) (first : Nat)
    (binding : ArmCertValue.SplitMemory.Bound view r first width (writeSegments calls)) (member : r ∈ regions) (fits : first + width ≤ 8 * r.words)
    (injective : Physical.RegionsInjective view regions)
    (payload : ∀ call ∈ calls, ∀ i, i < call.request.bytes →
      writeByte call i = ((u.eval s) >>> (8 * (call.request.offset + i))).setWidth 8) :
    F.StoreHolds view regions width u r first s t := by
  apply ArmCertValue.SplitMemory.storeHolds_of_writeCalls writeSegment writeByte calls view regions s t width u r first binding member fits injective payload
  rw [chain.memory,writeMemory_eq]

theorem writeChain_storePair {s t : NativeAccess.Trace.State} {calls : List NativeAccess.Trace.WriteCall} (chain : NativeAccess.Trace.WriteChain s calls t)
    (view : Physical.BytePA) (regions : List Region) (r : Region) (word : Nat) (rt rt2 : Reg)
    (binding : ArmCertValue.SplitMemory.Bound view r (8 * word) 16 (writeSegments calls)) (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words)
    (injective : Physical.RegionsInjective view regions)
    (payload : ∀ call ∈ calls, ∀ i, i < call.request.bytes → writeByte call i =
      (if call.request.offset + i < 8 then ArmCertValue.MemRegion.byteOf (regVal s rt) (call.request.offset + i)
        else ArmCertValue.MemRegion.byteOf (regVal s rt2) (call.request.offset + i - 8))) :
    Physical.MemVHolds view regions [.store rt r word,.store rt2 r (word + 1)] s t := by
  apply ArmCertValue.SplitMemory.storePair_of_writeCalls writeSegment writeByte calls view regions s t r word rt rt2 binding member fits injective payload
  rw [chain.memory,writeMemory_eq]

#print axioms writeMemory_eq
#print axioms writeCalls_frame_raw
#print axioms writeChain_frame
#print axioms writeChain_fragments
#print axioms writeChain_storeHolds
#print axioms writeChain_storePair
end ArmCertValue.NativeFragments
