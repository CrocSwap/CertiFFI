import ArmCertWalk.StructuralInputs
import ArmCertTranslateModel.Image

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Roles belong to observations/operations, never uniquely to a physical slot. -/
def leafUse : DescriptorRole → Bool
  | .table => false
  | .leaf => true

def effectiveAF (params : S1TTWParams) : DescriptorRole → Bool
  | .table => params.haft == 1#1
  | .leaf => params.ha == 1#1

theorem bv1_zero_of_ne_one (x : BitVec 1) (h : x ≠ 1#1) : x = 0#1 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hn : x.toNat ≠ 1 := by
    intro he
    exact h (BitVec.eq_of_toNat_eq he)
  change x.toNat = 0
  omega

theorem pie_zero_of_false (params : S1TTWParams) (h : (params.pie == 1#1) = false) :
    params.pie = 0#1 := by
  apply bv1_zero_of_ne_one
  intro he
  simp [he] at h

/-- Exact bridge to memory's structural readiness type; no new readiness
    condition or feature-absence premise is introduced. -/
theorem afReady_iff (params : S1TTWParams) (role : DescriptorRole) (d : BitVec 64) :
    ArmCertWalk.AFReady params role d ↔
      RoleReady (params.ha == 1#1) (leafUse role) d := by
  cases role <;>
    simp [ArmCertWalk.AFReady, RoleReady, DescriptorDelta.AFReady, leafUse, beq_iff_eq]

/-- Any permitted operation preserves readiness for EVERY use of the physical
    slot, even a leaf use aliasing a table update authorized through HAFT. -/
theorem allowed_preserves_ready (params : S1TTWParams) (operation observed : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params operation before after)
    (hr : ArmCertWalk.AFReady params observed before) :
    ArmCertWalk.AFReady params observed after := by
  obtain ⟨af, dirty, rfl, _, _⟩ := h
  cases observed
  · trivial
  · exact hr.elim (fun hb => Or.inl (source_af_mono af dirty before hb)) Or.inr

/-- Memory's exact source-function relation implies the precise raw bitmask
    relation. AF permission is role-specific; dirty permission remains leaf HA. -/
theorem allowed_delta (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after) :
    DescriptorDelta (effectiveAF params role) (params.hd == 1#1) (params.pie == 1#1) before after := by
  obtain ⟨af, dirty, rfl, haf, hd⟩ := h
  apply hardware_delta
  · intro ha
    have he := haf ha
    cases role <;> simpa [effectiveAF, updateAFEnabled] using he
  · intro hh
    obtain ⟨rfl, hha, hhd, hdbm⟩ := hd hh
    refine ⟨by simp [effectiveAF, hha], by simp [hhd], ?_⟩
    intro hp
    exact hdbm (pie_zero_of_false params hp)

/-- The source's permission-sensitive observer is retained, rather than merely
    dropping dirty-state bits and claiming all permissions stay equal. -/
theorem allowed_source_view (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after) :
    S1DescriptorPIE.view (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) after =
      S1DescriptorPIE.view (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) before := by
  obtain ⟨af, dirty, rfl, _, hd⟩ := h
  apply S1DescriptorPIE.hardware_view
  intro hh
  obtain ⟨_, hha, hhd, hdbm⟩ := hd hh
  refine ⟨by simp [hha], by simp [hhd], ?_⟩
  intro hp
  exact hdbm (pie_zero_of_false params hp)

/-- The actual structural AllowedUpdate type feeds the shared-role image
    invariant directly. Memory's source execution proof will produce this
    relation; a future-success or future-preservation callback is unnecessary. -/
theorem allowed_image_store (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (mem : Mem) (slot : Nat) (observe : RoleObservation)
    (h : AllowedUpdate params role before after)
    (hReal : ImageRealizes observe (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) mem)
    (hSlots : ImageAligned observe) (hAlign : slot % 8 = 0)
    (hDesc : S1ByteMemory.DescAt mem slot before) :
    ImageRealizes observe (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1)
      (S1ByteMemory.store mem slot after) := by
  obtain ⟨af, dirty, rfl, _, hd⟩ := h
  apply hReal.hardware_store hSlots slot before af dirty hAlign hDesc
  intro hh
  obtain ⟨_, hha, hhd, hdbm⟩ := hd hh
  refine ⟨by simp [hha], by simp [hhd], ?_⟩
  intro hp
  exact hdbm (pie_zero_of_false params hp)

#print axioms afReady_iff
#print axioms allowed_preserves_ready
#print axioms allowed_delta
#print axioms allowed_source_view
#print axioms allowed_image_store
end ArmCert.Translate.Model
