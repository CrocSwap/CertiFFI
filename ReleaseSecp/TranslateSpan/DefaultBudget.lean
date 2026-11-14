import TranslateSpan.SecpRawDeployment
import NativeAccess.PairGeometry

open Sail ArmFull ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace TranslateSpan.DefaultBudget
open SecpRawDeployment

def cost (address : BitVec 64) : Nat :=
  match NativeAccess.PairGeometry.selected address with
  | .one16 => 1
  | .two8 => 2
  | .bytes => 16

def before (p : Plan) (entry : NativeState) (k : Nat) : Nat :=
  (p.accesses.filter (fun a => a.index < k)).foldl
    (fun total a => total + cost (BitVec.addInt (entryGPR entry a.pin) a.offset)) 0

theorem cost_positive (address : BitVec 64) : 0 < cost address := by
  unfold cost
  cases NativeAccess.PairGeometry.selected address <;> decide

theorem cost_at_most (address : BitVec 64) : cost address ≤ 16 := by
  unfold cost
  cases NativeAccess.PairGeometry.selected address <;> decide

#print axioms cost_positive
#print axioms cost_at_most
end TranslateSpan.DefaultBudget
