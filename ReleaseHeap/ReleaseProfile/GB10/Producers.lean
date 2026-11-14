import ReleaseProfile.GB10.SourceSpec

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-!
# Shared GB10 entry-atom producers (generated; no DefaultHeapCards dependency)

Original card ReleaseProfile.DefaultHeapCards.card_normal, C1 5f34b4d98b44e2ce.
Of the 259 original input atoms, 214 are produced from the actual-entry agreement,
7 (timers) come from the named premise GB10.TimersQuiet (D264),
with the canonical source and 38 remain explicit inputs, each with its original
proposition at the source data substitution (catalogue and AttributeConfig are source
projections). The proof is the original card applied to every binder; no atom is dropped.
Spec, rows, mapping, pins, scope, image, loadBase, base, offsets and budget remain the
original card's program data; every config-bearing spec field remains pinned by a retained
atom to the source-determined actual entry.
-/

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

/-- Source control catalogue: exactly the four canonical control words. -/
def sourceCatalogue (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    NativeMteTagCheck.ControlCatalogue :=
  ⟨controlWord rho.val caller.caller .TCR_EL2, controlWord rho.val caller.caller .SCTLR_EL2,
   controlWord rho.val caller.caller .HCR_EL2, controlWord rho.val caller.caller .SCR_EL3⟩

/-- Source attribute configuration: MAIR/MAIR2 coordinates and the XS/MTE2 feature values. -/
def sourceAttributes (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    ArmCertWalk.AttributeConfig :=
  ⟨interpret rho.val caller.caller ⟨.bank_BitVec_64 .MAIR_EL2, rfl⟩,
   interpret rho.val caller.caller ⟨.bank_BitVec_64 .MAIR2_EL2, rfl⟩,
   FeatureSource.value rho.val.features 166, FeatureSource.value rho.val.features 134⟩

variable {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}

theorem feature_at (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) (i : Nat) (h : i < 259) (v : Bool) (a : AuthorityRef)
    (rec : FeatureSource.declared ⟨i, h⟩ = some (v, a)) : e.regs.FeatureImpl[i]! = v := by
  rw [getElem!_pos _ i h]
  exact (actual_coordinate cfg e.regs ag ⟨.feature ⟨i, h⟩, rfl⟩).trans
    (FeatureSource.value_declared _ _ v a rec)

theorem pstate_EL (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.EL = 0#2 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_EL, rfl⟩).trans caller.normal.el

theorem pstate_nRW (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.nRW = 0#1 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_nRW, rfl⟩).trans caller.normal.nrw

theorem pstate_A (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.A = 0#1 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_A, rfl⟩).trans caller.normal.alignment

theorem pstate_I (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.I = 0#1 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_I, rfl⟩).trans caller.normal.irq

theorem pstate_F (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.F = 0#1 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_F, rfl⟩).trans caller.normal.fiq

theorem pstate_IL (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.IL = 0#1 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_IL, rfl⟩).trans caller.normal.illegal

theorem pstate_SS (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.SS = 0#1 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_SS, rfl⟩).trans caller.normal.singleStep

theorem pstate_BTYPE (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.BTYPE = 0#2 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_BTYPE, rfl⟩).trans caller.normal.branchType

theorem pstate_TCO (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.PSTATE.TCO = 0#1 :=
  (actual_coordinate cfg e.regs ag ⟨.pstate_TCO, rfl⟩).trans caller.normal.tagCheckOverride

theorem control_entry (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) (key : ArmFull.Bank_BitVec_64) (h : isEntryData64 key = false := by decide) :
    e.regs.bank_BitVec_64 key = controlWord rho.val caller.caller key :=
  actual_control_word cfg e.regs ag key h

/-- beforeFetchState only rewrites MDCCSR_EL0 among 64-bit words (kernel-checked per key). -/
theorem control_before_HCR_EL2 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .HCR_EL2 =
      controlWord rho.val caller.caller .HCR_EL2 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .HCR_EL2, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .HCR_EL2, rfl⟩

theorem control_before_SCR_EL3 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .SCR_EL3 =
      controlWord rho.val caller.caller .SCR_EL3 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .SCR_EL3, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .SCR_EL3, rfl⟩

theorem control_before_SCTLR_EL2 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .SCTLR_EL2 =
      controlWord rho.val caller.caller .SCTLR_EL2 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .SCTLR_EL2, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .SCTLR_EL2, rfl⟩

theorem control_before_TCR_EL2 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2 =
      controlWord rho.val caller.caller .TCR_EL2 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .TCR_EL2, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .TCR_EL2, rfl⟩

theorem control_before_PMBLIMITR_EL1 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .PMBLIMITR_EL1 =
      controlWord rho.val caller.caller .PMBLIMITR_EL1 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .PMBLIMITR_EL1, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .PMBLIMITR_EL1, rfl⟩

theorem control_before_MDSCR_EL1 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .MDSCR_EL1 =
      controlWord rho.val caller.caller .MDSCR_EL1 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .MDSCR_EL1, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .MDSCR_EL1, rfl⟩

theorem control_before_BRBFCR_EL1 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .BRBFCR_EL1 =
      controlWord rho.val caller.caller .BRBFCR_EL1 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .BRBFCR_EL1, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .BRBFCR_EL1, rfl⟩

theorem control_before_MDCR_EL3 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .MDCR_EL3 =
      controlWord rho.val caller.caller .MDCR_EL3 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .MDCR_EL3, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .MDCR_EL3, rfl⟩

theorem control_before_PMINTENCLR_EL1 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .PMINTENCLR_EL1 =
      controlWord rho.val caller.caller .PMINTENCLR_EL1 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .PMINTENCLR_EL1, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .PMINTENCLR_EL1, rfl⟩

theorem control_before_TCR2_EL2 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR2_EL2 =
      controlWord rho.val caller.caller .TCR2_EL2 := by
  refine (beforeFetch_profile_frame e ⟨.bank_BitVec_64 .TCR2_EL2, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .TCR2_EL2, rfl⟩

theorem field_HCR_EL2_E2H (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .HCR_EL2) :
    ArmFull.Functions._get_HCR_EL2_Type_E2H word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_HCR_EL2_Type_E2H, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .HCR_EL2 ⟨34, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_HCR_EL2_TGE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .HCR_EL2) :
    ArmFull.Functions._get_HCR_EL2_Type_TGE word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_HCR_EL2_Type_TGE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .HCR_EL2 ⟨27, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_HCR_EL2_RW (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .HCR_EL2) :
    ArmFull.Functions._get_HCR_EL2_Type_RW word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_HCR_EL2_Type_RW, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .HCR_EL2 ⟨31, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCR_EL3_NS (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCR_EL3) :
    ArmFull.Functions._get_SCR_EL3_Type_NS word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCR_EL3_Type_NS, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCR_EL3 ⟨0, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCR_EL3_RW (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCR_EL3) :
    ArmFull.Functions._get_SCR_EL3_Type_RW word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCR_EL3_Type_RW, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCR_EL3 ⟨10, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCR_EL3_EEL2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCR_EL3) :
    ArmFull.Functions._get_SCR_EL3_Type_EEL2 word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCR_EL3_Type_EEL2, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCR_EL3 ⟨18, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCR_EL3_NSE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCR_EL3) :
    ArmFull.Functions._get_SCR_EL3_Type_NSE word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCR_EL3_Type_NSE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCR_EL3 ⟨62, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_EE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_EE word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_EE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨25, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_TCF0 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_TCF0 word = 0#2 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_TCF0, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨38, by decide⟩ false _ rfl rfl
  have b1 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨39, by decide⟩ false _ rfl rfl
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simpa [BitVec.getLsbD_eq_getElem] using b0
  · simpa [BitVec.getLsbD_eq_getElem] using b1

theorem field_TCR_EL2_TBI0 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .TCR_EL2) :
    ArmFull.Functions._get_TCR_EL2_Type_TBI0 word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_TCR_EL2_Type_TBI0, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨37, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_TCR_EL2_TBID0 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .TCR_EL2) :
    ArmFull.Functions._get_TCR_EL2_Type_TBID0 word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_TCR_EL2_Type_TBID0, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨51, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_TCR_EL2_TG0 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .TCR_EL2) :
    ArmFull.Functions._get_TCR_EL2_Type_TG0 word = 0#2 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_TCR_EL2_Type_TG0, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨14, by decide⟩ false _ rfl rfl
  have b1 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨15, by decide⟩ false _ rfl rfl
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simpa [BitVec.getLsbD_eq_getElem] using b0
  · simpa [BitVec.getLsbD_eq_getElem] using b1

theorem field_MDSCR_EL1_SS (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .MDSCR_EL1) :
    ArmFull.Functions._get_MDSCR_EL1_Type_SS word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_MDSCR_EL1_Type_SS, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .MDSCR_EL1 ⟨0, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_MDSCR_EL1_MDE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .MDSCR_EL1) :
    ArmFull.Functions._get_MDSCR_EL1_Type_MDE word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_MDSCR_EL1_Type_MDE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .MDSCR_EL1 ⟨15, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_PMBLIMITR_EL1_E (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .PMBLIMITR_EL1) :
    ArmFull.Functions._get_PMBLIMITR_EL1_Type_E word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_PMBLIMITR_EL1_Type_E, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .PMBLIMITR_EL1 ⟨0, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_BRBFCR_EL1_PAUSED (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .BRBFCR_EL1) :
    ArmFull.Functions._get_BRBFCR_EL1_Type_PAUSED word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_BRBFCR_EL1_Type_PAUSED, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .BRBFCR_EL1 ⟨7, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_MDCR_EL3_NSPB (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .MDCR_EL3) :
    ArmFull.Functions._get_MDCR_EL3_Type_NSPB word = 3#2 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_MDCR_EL3_Type_NSPB, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .MDCR_EL3 ⟨12, by decide⟩ true _ rfl rfl
  have b1 := rho.property.construction.control64 caller.caller .MDCR_EL3 ⟨13, by decide⟩ true _ rfl rfl
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simpa [BitVec.getLsbD_eq_getElem] using b0
  · simpa [BitVec.getLsbD_eq_getElem] using b1

theorem field_MDCR_EL3_NSPBE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .MDCR_EL3) :
    ArmFull.Functions._get_MDCR_EL3_Type_NSPBE word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_MDCR_EL3_Type_NSPBE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .MDCR_EL3 ⟨11, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_M (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_M word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_M, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨0, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_C (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_C word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_C, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨2, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_E0E (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_E0E word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_E0E, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨24, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCR_EL3_GCSEn (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCR_EL3) :
    ArmFull.Functions._get_SCR_EL3_Type_GCSEn word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCR_EL3_Type_GCSEn, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCR_EL3 ⟨39, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_A (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_A word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_A, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨1, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_I (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_I word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_I, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨12, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_SA (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_SA word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_SA, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨3, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_SA0 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_SA0 word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_SA0, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨4, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_nTWI (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_nTWI word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_nTWI, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨16, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_nTWE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_nTWE word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_nTWE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨18, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field_SCTLR_EL2_DZE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 64) (same : word = controlWord rho.val caller.caller .SCTLR_EL2) :
    ArmFull.Functions._get_SCTLR_EL2_Type_DZE word = 1#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_DZE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨14, by decide⟩ true _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem control32_entry (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) (key : ArmFull.Bank_BitVec_32) :
    e.regs.bank_BitVec_32 key = controlWord32 rho.val caller.caller key :=
  actual_coordinate cfg e.regs ag ⟨.bank_BitVec_32 key, rfl⟩

theorem field32_EDECR_RCE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 32) (same : word = controlWord32 rho.val caller.caller .EDECR) :
    ArmFull.Functions._get_EDECR_Type_RCE word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_EDECR_Type_RCE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control32 caller.caller .EDECR ⟨1, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field32_CTIDEVCTL_RCE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 32) (same : word = controlWord32 rho.val caller.caller .CTIDEVCTL) :
    ArmFull.Functions._get_CTIDEVCTL_Type_RCE word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_CTIDEVCTL_Type_RCE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control32 caller.caller .CTIDEVCTL ⟨1, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field32_EDSCR_HDE (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 32) (same : word = controlWord32 rho.val caller.caller ._EDSCR) :
    ArmFull.Functions._get_EDSCR_Type_HDE word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_EDSCR_Type_HDE, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control32 caller.caller ._EDSCR ⟨14, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem field32_CNTCR_SCEN (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (word : BitVec 32) (same : word = controlWord32 rho.val caller.caller .CNTCR) :
    ArmFull.Functions._get_CNTCR_Type_SCEN word = 0#1 := by
  subst same
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_CNTCR_Type_SCEN, Sail.BitVec.extractLsb] at hj ⊢
  have b0 := rho.property.construction.control32 caller.caller .CNTCR ⟨2, by decide⟩ false _ rfl rfl
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b0

theorem tcr_ds_before (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    Sail.BitVec.slice ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64
      ArmFull.Bank_BitVec_64.TCR_EL2) 59 1 = 0#1 := by
  rw [control_before_TCR_EL2 cfg e ag]
  have b := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨59, by decide⟩ false _ rfl rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have : j = 0 := by omega
  subst this
  simpa [Sail.BitVec.slice, BitVec.getLsbD_extractLsb', BitVec.getLsbD_eq_getElem] using b

theorem translation_enabled (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    ArmCertWalk.currentTranslationEnabled (ArmBridge.CruxGenGuarded.beforeFetchState e).regs = true := by
  unfold ArmCertWalk.currentTranslationEnabled
  rw [field_SCTLR_EL2_M _ _ _ (control_before_SCTLR_EL2 cfg e ag)]
  rfl

theorem dcache_entry (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : ArmCertWalk.currentDCache e.regs = true := by
  unfold ArmCertWalk.currentDCache
  rw [field_SCTLR_EL2_C _ _ _ (control_entry cfg e ag .SCTLR_EL2)]
  rfl

private theorem feature178_of_before (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs)
    (h : (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[178]! = true) :
    FeatureSource.value rho.val.features 178 = true := by
  have actual := actual_coordinate cfg e.regs ag ⟨.feature 178, rfl⟩
  have h' : e.regs.FeatureImpl[178]! = true := h
  rw [getElem!_pos _ 178 (by decide)] at h'
  exact actual.symm.trans h'

theorem tcr2_guard_D128 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[178]! = true →
      ArmFull.Functions._get_TCR2_EL2_Type_D128
        ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) = 0#1 := by
  intro h
  obtain ⟨b, -, -⟩ := rho.property.restrictions.tcr2Guard caller.caller (feature178_of_before cfg e ag h)
  have b' : (controlWord rho.val caller.caller .TCR2_EL2).getLsbD 5 = false := b
  rw [control_before_TCR2_EL2 cfg e ag]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_TCR2_EL2_Type_D128, Sail.BitVec.extractLsb] at hj ⊢
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b'

theorem tcr2_guard_AIE (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[178]! = true →
      ArmFull.Functions._get_TCR2_EL2_Type_AIE
        ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) = 0#1 := by
  intro h
  obtain ⟨-, b, -⟩ := rho.property.restrictions.tcr2Guard caller.caller (feature178_of_before cfg e ag h)
  have b' : (controlWord rho.val caller.caller .TCR2_EL2).getLsbD 4 = false := b
  rw [control_before_TCR2_EL2 cfg e ag]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_TCR2_EL2_Type_AIE, Sail.BitVec.extractLsb] at hj ⊢
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b'

theorem tcr2_guard_PnCH (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[178]! = true →
      ArmFull.Functions._get_TCR2_EL2_Type_PnCH
        ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) = 0#1 := by
  intro h
  obtain ⟨-, -, b⟩ := rho.property.restrictions.tcr2Guard caller.caller (feature178_of_before cfg e ag h)
  have b' : (controlWord rho.val caller.caller .TCR2_EL2).getLsbD 0 = false := b
  rw [control_before_TCR2_EL2 cfg e ag]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_TCR2_EL2_Type_PnCH, Sail.BitVec.extractLsb] at hj ⊢
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using b'

theorem num_breakpoints (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.bank_Int ArmFull.Bank_Int.NUM_BREAKPOINTS = 6 :=
  (actual_coordinate cfg e.regs ag ⟨.bank_Int .NUM_BREAKPOINTS, rfl⟩).trans
    (rho.property.construction.breakpoints caller.caller)

theorem num_watchpoints (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.bank_Int ArmFull.Bank_Int.NUM_WATCHPOINTS = 4 :=
  (actual_coordinate cfg e.regs ag ⟨.bank_Int .NUM_WATCHPOINTS, rfl⟩).trans
    (rho.property.construction.watchpoints caller.caller)

theorem num_ctx_breakpoints (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.bank_Int ArmFull.Bank_Int.__num_ctx_breakpoints = 2 :=
  (actual_coordinate cfg e.regs ag ⟨.bank_Int .__num_ctx_breakpoints, rfl⟩).trans
    (rho.property.construction.contextBreakpoints caller.caller)

private theorem pmu_cases (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    e.regs.bank_Int .NUM_PMU_COUNTERS = 6 ∨ e.regs.bank_Int .NUM_PMU_COUNTERS = 20 ∨
      e.regs.bank_Int .NUM_PMU_COUNTERS = 31 := by
  have actual := actual_coordinate cfg e.regs ag ⟨.bank_Int .NUM_PMU_COUNTERS, rfl⟩
  have restriction := rho.property.restrictions.pmuCountersTrm caller.caller
  revert restriction
  cases rho.val.coreKind <;> intro restriction
  · rcases restriction with h | h
    · exact Or.inl (actual.trans h)
    · exact Or.inr (Or.inr (actual.trans h))
  · rcases restriction with h | h
    · exact Or.inl (actual.trans h)
    · exact Or.inr (Or.inl (actual.trans h))

theorem pmu_lower (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : 0 ≤ e.regs.bank_Int ArmFull.Bank_Int.NUM_PMU_COUNTERS := by
  have h := pmu_cases cfg e ag
  omega

theorem pmu_upper (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.bank_Int ArmFull.Bank_Int.NUM_PMU_COUNTERS ≤ 31 := by
  have h := pmu_cases cfg e ag
  omega

theorem quiet_spe (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.bank_Bool ArmFull.Bank_Bool.SPESampleInFlight = false :=
  (actual_entryQuiescence cfg e.regs ag).speIdle

theorem quiet_edesr (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.EDESR = 0#32 :=
  (actual_entryQuiescence cfg e.regs ag).edesrClear

theorem quiet_osuc (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    ArmFull.Functions._get_EDESR_Type_OSUC (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.EDESR) = 0#1 :=
  (actual_entryQuiescence cfg e.regs ag).edesrOsuc

theorem quiet_branch (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.Branchtypetaken ≠ ArmFull.BranchType.BranchType_RESET :=
  (actual_entryQuiescence cfg e.regs ag).notReset

theorem quiet_emulator (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.__emulator_termination_opcode = none :=
  (actual_entryQuiescence cfg e.regs ag).noEmulatorStop

theorem quiet_btype_next (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : e.regs.BTypeNext = 0#2 :=
  (actual_entryQuiescence cfg e.regs ag).btypeNext

theorem quiet_tlb (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_Bool ArmFull.Bank_Bool.__tlb_enabled = false :=
  (actual_entryQuiescence cfg e.regs ag).tlbModelOff

theorem quiet_gic (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    e.regs.bank_Option_InterruptID ArmFull.Bank_Option_InterruptID.__GIC_Pending = none :=
  (actual_entryQuiescence cfg e.regs ag).gicIdle

theorem quiet_pmbsr (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    Sail.BitVec.extractLsb (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PMBSR_EL1) 17 17 = 0#1 :=
  (actual_entryQuiescence cfg e.regs ag).pmbsrS

theorem quiet_edscr_status (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    ArmFull.Functions._get_EDSCR_Type_STATUS (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) = 2#6 :=
  (actual_entryQuiescence cfg e.regs ag).edscrStatus

theorem pmintenclr_zero (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    ArmCert.HookQuiet.V0.reg64 e.regs ArmFull.Bank_BitVec_64.PMINTENCLR_EL1 = 0#64 := by
  show e.regs.bank_BitVec_64 .PMINTENCLR_EL1 = 0#64
  rw [control_entry cfg e ag .PMINTENCLR_EL1]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_zero]
  match i, hi with
  | 0, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨0, by decide⟩ false _ rfl rfl
  | 1, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨1, by decide⟩ false _ rfl rfl
  | 2, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨2, by decide⟩ false _ rfl rfl
  | 3, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨3, by decide⟩ false _ rfl rfl
  | 4, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨4, by decide⟩ false _ rfl rfl
  | 5, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨5, by decide⟩ false _ rfl rfl
  | 6, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨6, by decide⟩ false _ rfl rfl
  | 7, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨7, by decide⟩ false _ rfl rfl
  | 8, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨8, by decide⟩ false _ rfl rfl
  | 9, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨9, by decide⟩ false _ rfl rfl
  | 10, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨10, by decide⟩ false _ rfl rfl
  | 11, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨11, by decide⟩ false _ rfl rfl
  | 12, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨12, by decide⟩ false _ rfl rfl
  | 13, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨13, by decide⟩ false _ rfl rfl
  | 14, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨14, by decide⟩ false _ rfl rfl
  | 15, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨15, by decide⟩ false _ rfl rfl
  | 16, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨16, by decide⟩ false _ rfl rfl
  | 17, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨17, by decide⟩ false _ rfl rfl
  | 18, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨18, by decide⟩ false _ rfl rfl
  | 19, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨19, by decide⟩ false _ rfl rfl
  | 20, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨20, by decide⟩ false _ rfl rfl
  | 21, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨21, by decide⟩ false _ rfl rfl
  | 22, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨22, by decide⟩ false _ rfl rfl
  | 23, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨23, by decide⟩ false _ rfl rfl
  | 24, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨24, by decide⟩ false _ rfl rfl
  | 25, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨25, by decide⟩ false _ rfl rfl
  | 26, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨26, by decide⟩ false _ rfl rfl
  | 27, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨27, by decide⟩ false _ rfl rfl
  | 28, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨28, by decide⟩ false _ rfl rfl
  | 29, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨29, by decide⟩ false _ rfl rfl
  | 30, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨30, by decide⟩ false _ rfl rfl
  | 31, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨31, by decide⟩ false _ rfl rfl
  | 32, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨32, by decide⟩ false _ rfl rfl
  | 33, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨33, by decide⟩ false _ rfl rfl
  | 34, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨34, by decide⟩ false _ rfl rfl
  | 35, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨35, by decide⟩ false _ rfl rfl
  | 36, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨36, by decide⟩ false _ rfl rfl
  | 37, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨37, by decide⟩ false _ rfl rfl
  | 38, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨38, by decide⟩ false _ rfl rfl
  | 39, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨39, by decide⟩ false _ rfl rfl
  | 40, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨40, by decide⟩ false _ rfl rfl
  | 41, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨41, by decide⟩ false _ rfl rfl
  | 42, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨42, by decide⟩ false _ rfl rfl
  | 43, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨43, by decide⟩ false _ rfl rfl
  | 44, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨44, by decide⟩ false _ rfl rfl
  | 45, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨45, by decide⟩ false _ rfl rfl
  | 46, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨46, by decide⟩ false _ rfl rfl
  | 47, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨47, by decide⟩ false _ rfl rfl
  | 48, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨48, by decide⟩ false _ rfl rfl
  | 49, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨49, by decide⟩ false _ rfl rfl
  | 50, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨50, by decide⟩ false _ rfl rfl
  | 51, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨51, by decide⟩ false _ rfl rfl
  | 52, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨52, by decide⟩ false _ rfl rfl
  | 53, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨53, by decide⟩ false _ rfl rfl
  | 54, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨54, by decide⟩ false _ rfl rfl
  | 55, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨55, by decide⟩ false _ rfl rfl
  | 56, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨56, by decide⟩ false _ rfl rfl
  | 57, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨57, by decide⟩ false _ rfl rfl
  | 58, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨58, by decide⟩ false _ rfl rfl
  | 59, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨59, by decide⟩ false _ rfl rfl
  | 60, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨60, by decide⟩ false _ rfl rfl
  | 61, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨61, by decide⟩ false _ rfl rfl
  | 62, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨62, by decide⟩ false _ rfl rfl
  | 63, _ => exact rho.property.construction.control64 caller.caller .PMINTENCLR_EL1 ⟨63, by decide⟩ false _ rfl rfl
  | n + 64, h => exact absurd h (by omega)

theorem preparation (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : NativeMteTagCheck.PreparationAt (sourceCatalogue rho caller) e :=
  ⟨control_entry cfg e ag .TCR_EL2, control_entry cfg e ag .SCTLR_EL2, control_entry cfg e ag .HCR_EL2,
   control_entry cfg e ag .SCR_EL3⟩

theorem attribute_mair (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) :
    (sourceAttributes rho caller).mair =
      (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MAIR_EL2 := by
  refine ((beforeFetch_profile_frame e ⟨.bank_BitVec_64 .MAIR_EL2, rfl⟩
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)).trans ?_).symm
  exact actual_coordinate cfg e.regs ag ⟨.bank_BitVec_64 .MAIR_EL2, rfl⟩

theorem attribute_xs (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[166]! = (sourceAttributes rho caller).xs := by
  show e.regs.FeatureImpl[166]! = _
  rw [getElem!_pos _ 166 (by decide)]
  exact actual_coordinate cfg e.regs ag ⟨.feature 166, rfl⟩

theorem attribute_mte2 (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg e.regs) : (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[134]! = (sourceAttributes rho caller).mte2 := by
  show e.regs.FeatureImpl[134]! = _
  rw [getElem!_pos _ 134 (by decide)]
  exact actual_coordinate cfg e.regs ag ⟨.feature 134, rfl⟩

theorem controlWord_caller (u : Unknowns) (c1 c2 : Caller) (key : ArmFull.Bank_BitVec_64) :
    controlWord u c1 key = controlWord u c2 key := by
  by_cases h : isEntryData64 key = true
  · rw [controlWord_entry u c1 key h, controlWord_entry u c2 key h]
  · have h' := Bool.eq_false_iff.mpr h
    rw [controlWord_eq u c1 key h', controlWord_eq u c2 key h']
    exact interpret_caller_independent u c1 c2 ⟨.bank_BitVec_64 key, bank64_notData key h'⟩ rfl

/-- The shared CT catalogue does not depend on which admitted caller builds it. -/
theorem sourceCatalogue_caller (rho : AdmissibleSourceCompletion) (first second : AdmissibleCaller rho) :
    sourceCatalogue rho first = sourceCatalogue rho second := by
  simp only [sourceCatalogue, controlWord_caller rho.val first.caller second.caller]

theorem sourceAttributes_caller (rho : AdmissibleSourceCompletion) (first second : AdmissibleCaller rho) :
    sourceAttributes rho first = sourceAttributes rho second := by
  unfold sourceAttributes
  rw [interpret_caller_independent rho.val first.caller second.caller ⟨.bank_BitVec_64 .MAIR_EL2, rfl⟩ rfl,
    interpret_caller_independent rho.val first.caller second.caller ⟨.bank_BitVec_64 .MAIR2_EL2, rfl⟩ rfl]

theorem preparation_second (first : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : ArmBridge.Draft.NativeState) (ag : AgreesAt cfg e.regs) :
    NativeMteTagCheck.PreparationAt (sourceCatalogue rho first) e := by
  rw [sourceCatalogue_caller rho first caller]
  exact preparation cfg e ag

theorem attribute_mair_second (first : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : ArmBridge.Draft.NativeState) (ag : AgreesAt cfg e.regs) :
    (sourceAttributes rho first).mair = (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MAIR_EL2 := by
  rw [sourceAttributes_caller rho first caller]
  exact attribute_mair cfg e ag

theorem attribute_xs_second (first : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : ArmBridge.Draft.NativeState) (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[166]! = (sourceAttributes rho first).xs := by
  rw [sourceAttributes_caller rho first caller]
  exact attribute_xs cfg e ag

theorem attribute_mte2_second (first : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : ArmBridge.Draft.NativeState) (ag : AgreesAt cfg e.regs) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[134]! = (sourceAttributes rho first).mte2 := by
  rw [sourceAttributes_caller rho first caller]
  exact attribute_mte2 cfg e ag


end ReleaseProfile.GB10
