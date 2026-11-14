import ArmCertWalk.TranslateTxsz

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def currentTranslationEnabled (regs : Regs) : Bool :=
  _get_SCTLR_EL2_Type_M (regs.bank_BitVec_64 .SCTLR_EL2) == 1#1

theorem s1_enabled_el20_eq (kind : AccessType) (state : State) :
    AArch64_S1Enabled .Regime_EL20 kind state = .ok (currentTranslationEnabled state.regs) state := rfl

/-- The ignored 1274 parameter seed still changes the actual occurrence state.
It is retained before the SAME actual EL20 getter; it is not elided. -/
theorem get_params_el20_eq (ss : SecurityState) (va : BitVec 64) :
    AArch64_GetS1TTWParams .Regime_EL20 ss va = (do
      let _ ← undefined_S1TTWParams (← occLabel 1274) ()
      AArch64_S1TTWParamsEL20 ss (AArch64_GetVARange va)) := rfl

def sourceE0PDFault (params : S1TTWParams) (acc : AccessDescriptor) : Bool :=
  (acc.el == EL0) && (params.e0pd == 1#1)

def sourceTmeFault (regs : Regs) (params : S1TTWParams) (acc : AccessDescriptor) : Bool :=
  ((regs.FeatureImpl[227] && (acc.el == EL0)) && (params.nfd == 1#1)) && acc.transactional

def sourceVectorFault (regs : Regs) (params : S1TTWParams) (acc : AccessDescriptor) : Bool :=
  ((regs.FeatureImpl[81] && (acc.el == EL0)) && (params.nfd == 1#1)) &&
    ((acc.nonfault && acc.contiguous) || ((acc.firstfault && (!acc.first)) && (!acc.contiguous)))

def sourceTmeGuard {R : Type} (params : S1TTWParams) (acc : AccessDescriptor) : SailME R Bool := do
  pure ((← do pure ((← do pure ((← HaveTME ()) && (acc.el == EL0))) && (params.nfd == 1#1))) && acc.transactional)

def sourceVectorGuard {R : Type} (params : S1TTWParams) (acc : AccessDescriptor) : SailME R Bool := do
  pure ((← do pure ((← do pure ((← HaveSVE ()) && (acc.el == EL0))) && (params.nfd == 1#1))) &&
    ((acc.nonfault && acc.contiguous) || ((acc.firstfault && (!acc.first)) && (!acc.contiguous))))

theorem source_tme_guard_eq {R : Type} (params : S1TTWParams) (acc : AccessDescriptor) (state : State) :
    (sourceTmeGuard params acc : SailME R Bool) state = .ok (.ok (sourceTmeFault state.regs params acc)) state := rfl

theorem source_vector_guard_eq {R : Type} (params : S1TTWParams) (acc : AccessDescriptor) (state : State) :
    (sourceVectorGuard params acc : SailME R Bool) state = .ok (.ok (sourceVectorFault state.regs params acc)) state := rfl

/-- Pure source predicates for a declared actual query, AFTER the source TxSZ
normalization. Raw TxSZ fault selection is checked separately before that
normalization. No future call, callee result or preservation callback occurs. -/
structure TranslateQueryChecks (regs : Regs) (params : S1TTWParams) (va : BitVec 64)
    (acc : AccessDescriptor) : Prop where
  va : AArch64_VAIsOutOfRange va acc.acctype .Regime_EL20 params = false
  e0pd : sourceE0PDFault params acc = false
  tme : sourceTmeFault regs params acc = false
  vector : sourceVectorFault regs params acc = false

def checkTranslateQuery (regs : Regs) (params : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor) : Bool :=
  decide (AArch64_VAIsOutOfRange va acc.acctype .Regime_EL20 params = false) &&
    decide (sourceE0PDFault params acc = false) && decide (sourceTmeFault regs params acc = false) &&
    decide (sourceVectorFault regs params acc = false)

theorem check_translate_query_sound (regs : Regs) (params : S1TTWParams) (va : BitVec 64)
    (acc : AccessDescriptor) (checked : checkTranslateQuery regs params va acc = true) :
    TranslateQueryChecks regs params va acc := by
  simp only [checkTranslateQuery, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1.1.1, checked.1.1.2, checked.1.2, checked.2⟩

/-- Only these four extra getter fields are used by the outer source guards;
TxSZ and MTX already belong to the canonical geometry/image projection. -/
structure TranslateGuardView where
  tbi : BitVec 1
  tbid : BitVec 1
  nfd : BitVec 1
  e0pd : BitVec 1
  deriving DecidableEq

def translateGuardView (params : S1TTWParams) : TranslateGuardView :=
  ⟨params.tbi, params.tbid, params.nfd, params.e0pd⟩

theorem translate_guard_view_normalize (regs : Regs) (params : S1TTWParams) :
    translateGuardView (normalizeWalkParams regs params) = translateGuardView params := by
  by_cases low : (params.txsz.toNat : Int) < 16 <;>
    by_cases high : (params.txsz.toNat : Int) > currentMaxTxsz regs <;>
    simp [normalizeWalkParams, translateGuardView, low, high]

theorem TranslateQueryChecks.reparam (regs : Regs) (first second : S1TTWParams)
    (va : BitVec 64) (acc : AccessDescriptor) (txsz : first.txsz = second.txsz)
    (mtx : first.mtx = second.mtx) (guard : translateGuardView first = translateGuardView second)
    (current : TranslateQueryChecks regs first va acc) : TranslateQueryChecks regs second va acc := by
  have tbi : first.tbi = second.tbi := congrArg TranslateGuardView.tbi guard
  have tbid : first.tbid = second.tbid := congrArg TranslateGuardView.tbid guard
  have nfd : first.nfd = second.nfd := congrArg TranslateGuardView.nfd guard
  have e0pd : first.e0pd = second.e0pd := congrArg TranslateGuardView.e0pd guard
  have vaEq : AArch64_VAIsOutOfRange va acc.acctype .Regime_EL20 first =
      AArch64_VAIsOutOfRange va acc.acctype .Regime_EL20 second := by
    simp only [AArch64_VAIsOutOfRange, txsz, mtx, tbi, tbid]
  refine ⟨vaEq.symm.trans current.va, ?_, ?_, ?_⟩
  · simpa only [sourceE0PDFault, e0pd] using current.e0pd
  · simpa only [sourceTmeFault, nfd] using current.tme
  · simpa only [sourceVectorFault, nfd] using current.vector

#print axioms s1_enabled_el20_eq
#print axioms get_params_el20_eq
#print axioms source_tme_guard_eq
#print axioms source_vector_guard_eq
#print axioms check_translate_query_sound
#print axioms translate_guard_view_normalize
#print axioms TranslateQueryChecks.reparam
end ArmCertWalk
