import ArmCertWalk.LeafFinishSource
import ArmCertWalk.PermissionBitFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def leafFinished (current prepared : TTWState) (permissions : Permissions)
    (descriptor : BitVec 64) : TTWState :=
  { prepared with
    permissions := permissions
    s1assured := false
    contiguous := if current.disch == 1#1 then 0#1 else BitVec.ofBool (descriptor.getLsbD 52)
    nG := BitVec.ofBool (descriptor.getLsbD 11)
    guardedpage := BitVec.ofBool (descriptor.getLsbD 50) }

def LeafFinishEffect (expected : TTWState) (state : State) :
    EStateM.Result (Sail.Error exception) State TTWState → Prop
  | .ok actual other => actual = expected ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem leaf_finish_effect (current : TTWState) (s2 : Bool) (params : S1TTWParams)
    (descriptor : BitVec 64) (prepared : TTWState) (permissions : Permissions) (state : State)
    (d128 : params.d128 = 0#1) (pnch : params.pnch = 0#1) (tg : params.tgx = .TGx_4KB)
    (positive : 1 ≤ current.level) (level : current.level ≤ 3) :
    LeafFinishEffect (leafFinished current prepared permissions descriptor) state
      (LeafNextStages.finish current s2 params descriptor prepared permissions state) := by
  rw [LeafFinishSource.complete current s2 params descriptor prepared permissions state d128 pnch tg positive level]
  have nonzero : current.level ≠ 0 := by omega
  have bit52 := source_permission_bit_unextended descriptor 52 (by decide)
  have bit11 := source_permission_bit_unextended descriptor 11 (by decide)
  have bit50 := source_permission_bit_unextended descriptor 50 (by decide)
  observe_simp [LeafFinishEffect, leafFinished, LeafFinishSource.native]
  all_goals simp [nonzero, bit52, bit11, bit50]

theorem leaf_finish_total (current : TTWState) (s2 : Bool) (params : S1TTWParams)
    (descriptor : BitVec 64) (prepared : TTWState) (permissions : Permissions) (state : State)
    (d128 : params.d128 = 0#1) (pnch : params.pnch = 0#1) (tg : params.tgx = .TGx_4KB)
    (positive : 1 ≤ current.level) (level : current.level ≤ 3) :
    ∃ other, LeafNextStages.finish current s2 params descriptor prepared permissions state =
      .ok (leafFinished current prepared permissions descriptor) other ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  have effect := leaf_finish_effect current s2 params descriptor prepared permissions state d128 pnch tg positive level
  cases actual : LeafNextStages.finish current s2 params descriptor prepared permissions state with
  | error err other => simp only [actual, LeafFinishEffect] at effect
  | ok answer other =>
    have detail := by simpa only [actual, LeafFinishEffect] using effect
    exact ⟨other, by rw [← detail.1], detail.2⟩

#print axioms leaf_finish_total
end ArmCertWalk
