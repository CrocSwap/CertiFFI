import ArmCertWalk.TranslateChoiceInputs
import ArmCertWalk.RootGeometry

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- The actual small-table feature query sets the source maximum. Both values
are retained; this is not a TTST implementation pin. -/
def currentMaxTxsz (regs : Regs) : Int := if regs.FeatureImpl[122] then 48 else 39

def normalizeTxsz (regs : Regs) (txsz : BitVec 6) : BitVec 6 :=
  if (txsz.toNat : Int) < 16 then integer_subrange 16 5 0
  else if (txsz.toNat : Int) > currentMaxTxsz regs then integer_subrange (currentMaxTxsz regs) 5 0
  else txsz

def normalizeWalkParams (regs : Regs) (params : S1TTWParams) : S1TTWParams :=
  if (params.txsz.toNat : Int) < 16 then {params with txsz := integer_subrange 16 5 0}
  else if (params.txsz.toNat : Int) > currentMaxTxsz regs then
    {params with txsz := integer_subrange (currentMaxTxsz regs) 5 0}
  else params

def sourceTxszFault (regs : Regs) (params : S1TTWParams) : Bool :=
  if (params.txsz.toNat : Int) < 16 then regs.FeatureImpl[71] else false

theorem normalize_walk_txsz (regs : Regs) (params : S1TTWParams) :
    (normalizeWalkParams regs params).txsz = normalizeTxsz regs params.txsz := by
  by_cases low : (params.txsz.toNat : Int) < 16 <;>
    by_cases high : (params.txsz.toNat : Int) > currentMaxTxsz regs <;>
    simp [normalizeWalkParams, normalizeTxsz, low, high]
  all_goals rfl

theorem min_txsz_eq (params : S1TTWParams) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB) :
    AArch64_S1MinTxSZ .Regime_EL20 params.d128 params.ds params.tgx state = .ok 16 state := by
  have va56 : ∃ value, Have56BitVAExt () state = .ok value state := ⟨_, rfl⟩
  have va52 : ∃ value, Have52BitVAExt () state = .ok value state := ⟨_, rfl⟩
  obtain ⟨va56, call56⟩ := va56
  obtain ⟨va52, call52⟩ := va52
  have notD128 : ((0#1 : BitVec 1) == 1#1) = false := rfl
  have not64 : ((.TGx_4KB : TGx) == .TGx_64KB) = false := rfl
  simp [AArch64_S1MinTxSZ, d128, ds, tg, call56, call52, notD128, not64,
    Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

theorem small_tables_eq (state : State) :
    HaveSmallTranslationTableExt () state = .ok state.regs.FeatureImpl[122] state := rfl

theorem max_txsz_eq (state : State) :
    AArch64_MaxTxSZ .TGx_4KB state = .ok (currentMaxTxsz state.regs) state := by
  cases flag : state.regs.FeatureImpl[122] <;>
    simp [AArch64_MaxTxSZ, small_tables_eq, currentMaxTxsz, flag,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

/- These are TWO specific FINAL-model implementation choices, not a claim
about arbitrary implementation-defined Booleans or hardware. -/
drive_spec txsz_below_native, txsz_below_eq : fun (state : State) =>
  __IMPDEF_boolean "Fault on TxSZ value below minimum" state

drive_spec txsz_above_native, txsz_above_eq : fun (state : State) =>
  __IMPDEF_boolean "Fault on TxSZ value above maximum" state

theorem txsz_below_choice : __IMPDEF_boolean "Fault on TxSZ value below minimum" = (pure false : SailM Bool) := by
  funext state
  rw [txsz_below_eq]
  delta txsz_below_native
  rfl

theorem txsz_above_choice : __IMPDEF_boolean "Fault on TxSZ value above maximum" = (pure false : SailM Bool) := by
  funext state
  rw [txsz_above_eq]
  delta txsz_above_native
  rfl

theorem txsz_fault_eq (params : S1TTWParams) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB) :
    AArch64_S1TxSZFaults .Regime_EL20 params state = .ok (sourceTxszFault state.regs params) state := by
  have minCall := min_txsz_eq params state d128 ds tg
  simp only [d128, ds, tg] at minCall
  have maxCall := max_txsz_eq state
  have lvaCall : Have52BitVAExt () state = .ok state.regs.FeatureImpl[71] state := rfl
  by_cases low : (params.txsz.toNat : Int) < 16
  all_goals
    cases flag : state.regs.FeatureImpl[71] <;>
    simp [AArch64_S1TxSZFaults, d128, ds, minCall, tg, maxCall, sourceTxszFault, low,
      lvaCall, flag, txsz_below_choice, txsz_above_choice, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

#print axioms normalize_walk_txsz
#print axioms min_txsz_eq
#print axioms small_tables_eq
#print axioms max_txsz_eq
#print axioms txsz_below_eq
#print axioms txsz_above_eq
#print axioms txsz_below_choice
#print axioms txsz_above_choice
#print axioms txsz_fault_eq
end ArmCertWalk
