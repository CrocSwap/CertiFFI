import ArmCertWalk.LeafPrepareSource
import ArmCertWalk.LeafBaseCanonical

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def leafAttributeIndex (descriptor : BitVec 64) : BitVec 4 :=
  0#1 +++ Sail.BitVec.extractLsb descriptor 4 2

def leafShareability (descriptor : BitVec 64) : BitVec 2 :=
  Sail.BitVec.extractLsb descriptor 9 8

def leafPrepared (current seed : TTWState) (base : FullAddress) (word : BitVec 56) : TTWState :=
  { seed with
    istable := false
    level := current.level
    baseaddress := {base with address := word, paspace := .PAS_NonSecure} }

def LeafPrepareEffect (expected : TTWState × BitVec 4 × BitVec 2) (state : State) :
    EStateM.Result (Sail.Error exception) State (TTWState × BitVec 4 × BitVec 2) → Prop
  | .ok actual other => actual = expected ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem leaf_prepare_effect (current : TTWState) (s2 : Bool) (params : S1TTWParams)
    (descriptor : BitVec 64) (seed : TTWState) (base : FullAddress) (word : BitVec 56)
    (state : State) (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (aie : params.aie = 0#1) (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) :
    LeafPrepareEffect (leafPrepared current seed base word, leafAttributeIndex descriptor,
      leafShareability descriptor) state
      (LeafNextStages.prepare current s2 params descriptor seed base word state) := by
  rw [LeafPrepareSource.complete current s2 params descriptor seed base word state nonsecure aie d128 ds]
  observe_simp [LeafPrepareEffect, leafPrepared, leafAttributeIndex, leafShareability,
    LeafPrepareSource.native]

theorem leaf_prepare_total (current : TTWState) (s2 : Bool) (params : S1TTWParams)
    (descriptor : BitVec 64) (seed : TTWState) (base : FullAddress) (word : BitVec 56)
    (state : State) (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (aie : params.aie = 0#1) (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) :
    ∃ other, LeafNextStages.prepare current s2 params descriptor seed base word state =
      .ok (leafPrepared current seed base word, leafAttributeIndex descriptor,
        leafShareability descriptor) other ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have effect := leaf_prepare_effect current s2 params descriptor seed base word state nonsecure aie d128 ds
  cases actual : LeafNextStages.prepare current s2 params descriptor seed base word state with
  | error err other => simp only [actual, LeafPrepareEffect] at effect
  | ok answer other =>
    have detail := by simpa only [actual, LeafPrepareEffect] using effect
    exact ⟨other, by rw [← detail.1], detail.2⟩

theorem leaf_index_canonical (descriptor : BitVec 64) :
    ((leafAttributeIndex descriptor).toNat : Int) = S1MAIRKernel.index descriptor := by rfl

#print axioms leaf_prepare_total
#print axioms leaf_index_canonical
end ArmCertWalk
