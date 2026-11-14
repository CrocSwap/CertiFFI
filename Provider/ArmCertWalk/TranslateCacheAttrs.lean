import ArmCertWalk.TranslateCacheData

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk
open S1NormalME

private theorem instruction_nc_fields (acc : AccessDescriptor) (next : TTWState) :
    Ensures (fun _ => True) (TranslateOutputParts.selection .Regime_EL20 acc next true) NormalNCFields := by
  unfold TranslateOutputParts.selection
  simp only [↓reduceIte]
  apply bind_ensures _ _ _ _ _ normal_nc_fields_ensures
  intro attrs fields
  exact pure_ensures _ _ _ fields

private theorem output_mte_normal : S1Normality.Normal (HaveMTE2Ext ()) := by
  intro state
  exact ⟨_, state, rfl, rfl, rfl, rfl⟩

private theorem output_tagged_normal : S1Normality.Normal (ConstrainUnpredictableBool .Unpredictable_S1CTAGGED) := by
  unfold ConstrainUnpredictableBool
  apply S1Normality.bind_normal _ _ (S1Normality.occ_normal 514)
  intro label
  exact S1EntryCalleesExtra.bool_normal label

private theorem data_nc_fields (acc : AccessDescriptor) (next : TTWState)
    (notFetch : (acc.acctype == .AccessType_IFETCH) = false)
    (normal : next.memattrs.memtype = .MemType_Normal) :
    Ensures (fun regs => currentDCache regs = false)
      (TranslateOutputParts.selection .Regime_EL20 acc next false) NormalNCFields := by
  have ordinary : (acc.acctype != .AccessType_IFETCH) = true := by
    change (!(acc.acctype == .AccessType_IFETCH)) = true
    rw [notFetch]
    rfl
  have isNormal : ((.MemType_Normal : MemType) == .MemType_Normal) = true := rfl
  unfold TranslateOutputParts.selection
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply bind_ensures _ _ _ (fun value => value = true)
  · intro state current
    have cacheCall := dcache_el20_eq state
    rw [current] at cacheCall
    refine ⟨true, state, ?_, ⟨rfl, rfl, rfl⟩, rfl⟩
    simp [ordinary, normal, isNormal, cacheCall, Bind.bind, Pure.pure, Functor.map,
      ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
      EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  · intro selected equal
    subst selected
    simp only [↓reduceIte]
    apply bind_ensures _ _ _ NormalNCFields
    · intro state _
      exact normal_nc_fields_ensures state trivial
    · intro attrs fields
      apply bind_ensures _ _ _ (fun _ => True)
      · repeat first
          | exact normal_pure _ _
          | exact lift_normal _ _ output_mte_normal
          | exact lift_normal _ _ output_tagged_normal
          | apply normal_ite
          | apply normal_bind
          | intro x
      · intro tagChoice _
        apply pure_ensures
        split <;> exact fields

/-- Derive the final LS64 guard from current source I/C fields. Both cache
values and the real source MTE/tag choices are retained for ordinary accesses;
LS64's actual NC requirement is checked, not silently excluded. -/
theorem output_attrs_admissible_total (acc : AccessDescriptor) (next : TTWState) (state : State)
    (normal : next.memattrs.memtype = .MemType_Normal) (admissible : OutputCacheAdmissible acc state.regs) :
    ∃ attrs other,
      TranslateOutputParts.selection .Regime_EL20 acc next (instructionOutputNC acc state.regs) state =
        .ok (.ok attrs) other ∧ S1Normality.Frame state other ∧
      attrs.memtype = .MemType_Normal ∧ OutputExclusiveAdmissible acc attrs := by
  by_cases ls64 : acc.ls64 = true
  · have cache := admissible ls64
    cases fetch : acc.acctype == .AccessType_IFETCH with
    | true =>
      simp only [fetch, ↓reduceIte] at cache
      obtain ⟨attrs, other, call, frame, fields⟩ := instruction_nc_fields acc next state trivial
      refine ⟨attrs, other, ?_, frame, fields.1, fun _ => fields.2⟩
      simpa only [instructionOutputNC, fetch, ↓reduceIte, cache, Bool.not_false] using call
    | false =>
      simp only [fetch, Bool.false_eq_true, ↓reduceIte] at cache
      obtain ⟨attrs, other, call, frame, fields⟩ := data_nc_fields acc next fetch normal state cache
      refine ⟨attrs, other, ?_, frame, fields.1, fun _ => fields.2⟩
      simpa only [instructionOutputNC, fetch, Bool.false_eq_true, ↓reduceIte] using call
  · obtain ⟨attrs, other, call, frame, fields⟩ :=
      output_attrs_ensures acc next (instructionOutputNC acc state.regs) normal state trivial
    exact ⟨attrs, other, call, frame, fields, fun active => False.elim (ls64 active)⟩

#print axioms output_attrs_admissible_total
end ArmCertWalk
