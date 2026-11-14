import ReleaseProfile.GB10.Source

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024

/-!
# Domain inhabitation for both FEAT_MTE2 values (D260; dfc1 seal item)

The admissible completion domain contains completions with FEAT_MTE2 (feature 134, unresolved for both core
kinds) true and false. Mathematical consistency only; no invocation completion is selected.
-/

namespace ReleaseProfile.GB10.DomainWitness

open ReleaseProfile.MachineSource ReleaseProfile.GB10

/-- Domain-inhabitation example values; private and never an invocation's completion. -/
private def witnessValue : (c : RawCoordinate) → RawCoordinate.Value c := by
  intro c
  cases c <;> (dsimp only [RawCoordinate.Value]; exact default)

/-- Domain-inhabitation example register values (TRM option 6 for the PMU count). -/
private def witnessRegister : (c : RawCoordinate) → RawCoordinate.Value c
  | .bank_Int .NUM_PMU_COUNTERS => (6 : Int)
  | c => witnessValue c

private def witnessControl32 (key : ArmFull.Bank_BitVec_32) (index : Fin 32) : Bool :=
  match key with
  | ._EDSCR => index.val == 1
  | _ => false

private def witnessUnknowns (mte2 : Bool) : Unknowns where
  features := fun index _ => if index.val = 134 then mte2 else false
  registers := fun c _ => witnessRegister c
  controls := fun _ _ _ => false
  controls32 := fun key index _ => witnessControl32 key index
  coreKind := .x925

private theorem witness_edscr (mte2 : Bool) (caller : Caller) (index : Fin 32)
    (notDeclared : controlDeclared32 ._EDSCR index.val = none) :
    (controlWord32 (witnessUnknowns mte2) caller ._EDSCR).getLsbD index.val = (index.val == 1) :=
  interpret_control32_unresolved (witnessUnknowns mte2) caller ._EDSCR rfl coordinates32__EDSCR index notDeclared

private theorem witness_restrictions (mte2 : Bool) : SourceRestrictions (witnessUnknowns mte2) where
  tcr2Guard _ feature :=
    absurd ((FeatureSource.value_declared _ 178 false _ rfl).symm.trans feature) Bool.false_ne_true
  pmuCountersTrm caller := Or.inl rfl
  entryQuiescence caller := {
    speIdle := rfl
    notReset := by intro same; cases same
    noEmulatorStop := rfl
    btypeNext := rfl
    tlbModelOff := rfl
    gicIdle := rfl
    edscrStatus := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using witness_edscr mte2 caller ⟨0, by decide⟩ rfl
      · simpa using witness_edscr mte2 caller ⟨1, by decide⟩ rfl
      · simpa using witness_edscr mte2 caller ⟨2, by decide⟩ rfl
      · simpa using witness_edscr mte2 caller ⟨3, by decide⟩ rfl
      · simpa using witness_edscr mte2 caller ⟨4, by decide⟩ rfl
      · simpa using witness_edscr mte2 caller ⟨5, by decide⟩ rfl
    edesrClear := rfl
    edesrOsuc := by
      show Sail.BitVec.extractLsb (0#32 : BitVec 32) 0 0 = 0#1
      decide
    pmbsrS := by
      show Sail.BitVec.extractLsb (0#64 : BitVec 64) 17 17 = 0#1
      decide }

#check "CURRENT_DECL GB10.DomainWitness.sourceDomain_mte2"
/-- For each value of FEAT_MTE2 there is an admissible completion carrying it. -/
theorem sourceDomain_mte2 (mte2 : Bool) :
    ∃ rho : AdmissibleSourceCompletion, FeatureSource.value rho.val.features 134 = mte2 :=
  ⟨⟨witnessUnknowns mte2, ⟨constructionFacts_holds _, witness_restrictions mte2⟩⟩,
    (FeatureSource.value_unresolved _ 134 rfl).trans (show (if (134 : Fin 259).val = 134 then mte2 else false) = mte2 from if_pos rfl)⟩

end ReleaseProfile.GB10.DomainWitness

#print axioms ReleaseProfile.GB10.DomainWitness.sourceDomain_mte2
