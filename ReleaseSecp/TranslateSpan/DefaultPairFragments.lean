import TranslateSpan.DefaultAccessTrace
import ArmCertValue.NativeFragments
set_option autoImplicit false
namespace TranslateSpan.DefaultPairFragments
open TranslateSpan.DefaultAccessTrace NativeMteTagCheck ArmCertValue.SplitMemory

def writeSegment (call : WriteCall) : Segment :=
  ⟨call.request.offset,call.packet.ad.paddress.address.toNat,call.request.bytes⟩

def writeSegments (calls : List WriteCall) : List Segment := calls.map writeSegment

def writeByte (call : WriteCall) (j : Nat) : BitVec 8 :=
  (Sail.BitVec.castWidth (m := 8 * call.request.bytes) call.packet.data).extractLsb' (8 * j) 8

theorem writeMemory_eq (calls : List WriteCall) (mem : RAM) :
    writeMemory calls mem = writeCalls writeSegment writeByte calls mem := by
  induction calls generalizing mem with
  | nil => rfl
  | cons call rest ih =>
    rw [writeMemory,writeCalls]
    exact ih _

theorem writeChain_frame {s t : NativeMteTagCheck.State} {calls : List WriteCall} (chain : WriteChain s calls t) :
    ∀ pa, ¬ Writes (writeSegments calls) pa → t.mem[pa]? = s.mem[pa]? := by
  intro pa outside
  rw [chain.memory,writeMemory_eq]
  exact ArmCertValue.NativeFragments.writeCalls_frame_raw writeSegment writeByte calls s.mem pa outside

#print axioms writeMemory_eq
#print axioms writeChain_frame
end TranslateSpan.DefaultPairFragments
