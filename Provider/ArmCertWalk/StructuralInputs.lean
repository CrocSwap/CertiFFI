import ArmCertWalk.Profile
import Pilot.S1Descriptor

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

inductive DescriptorRole where
  | table
  | leaf
  deriving DecidableEq, Repr

/-- Table AF is ignored when HAFT is disabled; leaf AF gates the access. This
condition alone does not assert permissions, range validity or native success. -/
def AFReady (params : S1TTWParams) (role : DescriptorRole) (descriptor : BitVec 64) : Prop :=
  match role with
  | .table => True
  | .leaf => descriptor.getLsbD 10 = true ∨ params.ha = 1#1

def updateAFEnabled (params : S1TTWParams) : DescriptorRole → Prop
  | .table => params.haft = 1#1
  | .leaf => params.ha = 1#1

/-- Exact word update form with source authorization. Whether an actual write
occurs, its fault/permission checks, and event order are execution conclusions. -/
def AllowedUpdate (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) : Prop :=
  ∃ af dirty : Bool,
    after = S1Descriptor.hardwareUpdate af dirty before ∧
    (af = true → updateAFEnabled params role) ∧
    (dirty = true → role = .leaf ∧ params.ha = 1#1 ∧ params.hd = 1#1 ∧
      (params.pie = 0#1 → before.getLsbD 51 = true))

theorem allowedUpdate_refl (params : S1TTWParams) (role : DescriptorRole)
    (descriptor : BitVec 64) : AllowedUpdate params role descriptor descriptor := by
  exact ⟨false, false, rfl, by simp, by simp⟩

theorem allowedUpdate_other {params : S1TTWParams} {role : DescriptorRole}
    {before after : BitVec 64} (allowed : AllowedUpdate params role before after)
    (index : Nat) (notAF : index ≠ 10) (notDirty : index ≠ 7) :
    after.getLsbD index = before.getLsbD index := by
  obtain ⟨af, dirty, rfl, _, _⟩ := allowed
  cases af <;> cases dirty <;>
    simp [S1Descriptor.hardwareUpdate, S1Descriptor.setAF_other,
      S1Descriptor.setDirty_other, notAF, notDirty]

#print axioms allowedUpdate_refl
#print axioms allowedUpdate_other

end ArmCertWalk
