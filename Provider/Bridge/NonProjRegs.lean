import ArmFull.Defs

/-!
# CT2 native frame: `NonProjRegsEq`

B1 (non-projected architectural state UNCHANGED) and B4 (bookkeeping, path-determined) PARTITION
the native register file. A field is masked (= excluded from B1) iff it is either
* PROJECTED by `projectM` (gpr, SP_EL0, _PC, PSTATE.N/Z/C/V), or
* BOOKKEEPING (B4): the explicit non-bank fields below, PSTATE.BTYPE, and the bank keys selected
 by `BkKeys` (instantiated verbatim by from its E20/E22 write sets: PMU counters, BRBTS,
  clock fields, timer CTL/ISTATUS, EventRegister, __GIC_Pending, SEE, __ThisInstr, EDSCR/MDCCSR
  pipeline bits, InGuardedPage, SPE sampling, ...).
EVERY other field (all of _Z/_P/_FFR/_ZA/_ZT0, FPCR/FPSR, SP_EL1..3, FeatureImpl, all other
PSTATE fields incl. DIT, every unselected bank key, ...) must be EQUAL: the mask makes this complete
by construction, so no field can be silently omitted.
-/

open ArmFull

namespace ArmCertCT.CT2

/-- Bookkeeping bank keys (B4), one Bool predicate per register bank. -/
structure BkKeys where
  b32 : Bank_BitVec_32 → Bool
  v32_16 : Bank_Vector_BitVec_32_16 → Bool
  v32_4 : Bank_Vector_BitVec_32_4 → Bool
  v64_32 : Bank_Vector_BitVec_64_32 → Bool
  b64 : Bank_BitVec_64 → Bool
  v64_16 : Bank_Vector_BitVec_64_16 → Bool
  v64_4 : Bank_Vector_BitVec_64_4 → Bool
  v32_31 : Bank_Vector_BitVec_32_31 → Bool
  bool : Bank_Bool → Bool
  int : Bank_Int → Bool
  b1 : Bank_BitVec_1 → Bool
  b56 : Bank_BitVec_56 → Bool
  b16 : Bank_BitVec_16 → Bool
  b4 : Bank_BitVec_4 → Bool
  b128 : Bank_BitVec_128 → Bool
  vbool32 : Bank_Vector_Bool_32 → Bool
  v64_64 : Bank_Vector_BitVec_64_64 → Bool
  irq : Bank_Option_InterruptID → Bool
  b8 : Bank_BitVec_8 → Bool
  b2 : Bank_BitVec_2 → Bool
  v64_7 : Bank_Vector_BitVec_64_7 → Bool
  signal : Bank_Signal → Bool

@[inline] def maskBank {κ α : Type} [Inhabited α] (bk : κ → Bool) (m : κ → α) : κ → α :=
  fun k => if bk k then default else m k

/-- Zero the projected and bookkeeping fields of PSTATE (N, Z, C, V projected; BTYPE bookkeeping). -/
def maskPSTATE (ps : ProcState) : ProcState :=
  { ps with N := 0, Z := 0, C := 0, V := 0, BTYPE := 0 }

/-- Mask the projected and bookkeeping fields; everything else is kept. -/
def mask (bk : BkKeys) (r : Regs) : Regs :=
  { r with
    -- projected (A)
    gpr := default, SP_EL0 := 0, _PC := 0, PSTATE := maskPSTATE r.PSTATE,
    -- bookkeeping (B4), non-bank
    __BranchTaken := false, Branchtypetaken := default, __ThisInstrEnc := default,
    BTypeCompatible := false, BTypeNext := 0, ShouldAdvanceSS := false, ShouldAdvanceIT := false,
    PhysicalCount := 0, PMULastThresholdValue := default, PMUEventAccumulator := default,
    PMEVCNTSVR_EL1 := default, SPESampleCounter := default, SPERecordData := default,
    __SPE_LFSR := 0, SPESampleOpType := default, __emulator_termination_opcode := none,
    -- bookkeeping (B4), bank keys
    bank_BitVec_32 := maskBank bk.b32 r.bank_BitVec_32,
    bank_Vector_BitVec_32_16 := maskBank bk.v32_16 r.bank_Vector_BitVec_32_16,
    bank_Vector_BitVec_32_4 := maskBank bk.v32_4 r.bank_Vector_BitVec_32_4,
    bank_Vector_BitVec_64_32 := maskBank bk.v64_32 r.bank_Vector_BitVec_64_32,
    bank_BitVec_64 := maskBank bk.b64 r.bank_BitVec_64,
    bank_Vector_BitVec_64_16 := maskBank bk.v64_16 r.bank_Vector_BitVec_64_16,
    bank_Vector_BitVec_64_4 := maskBank bk.v64_4 r.bank_Vector_BitVec_64_4,
    bank_Vector_BitVec_32_31 := maskBank bk.v32_31 r.bank_Vector_BitVec_32_31,
    bank_Bool := maskBank bk.bool r.bank_Bool,
    bank_Int := maskBank bk.int r.bank_Int,
    bank_BitVec_1 := maskBank bk.b1 r.bank_BitVec_1,
    bank_BitVec_56 := maskBank bk.b56 r.bank_BitVec_56,
    bank_BitVec_16 := maskBank bk.b16 r.bank_BitVec_16,
    bank_BitVec_4 := maskBank bk.b4 r.bank_BitVec_4,
    bank_BitVec_128 := maskBank bk.b128 r.bank_BitVec_128,
    bank_Vector_Bool_32 := maskBank bk.vbool32 r.bank_Vector_Bool_32,
    bank_Vector_BitVec_64_64 := maskBank bk.v64_64 r.bank_Vector_BitVec_64_64,
    bank_Option_InterruptID := maskBank bk.irq r.bank_Option_InterruptID,
    bank_BitVec_8 := maskBank bk.b8 r.bank_BitVec_8,
    bank_BitVec_2 := maskBank bk.b2 r.bank_BitVec_2,
    bank_Vector_BitVec_64_7 := maskBank bk.v64_7 r.bank_Vector_BitVec_64_7,
    bank_Signal := maskBank bk.signal r.bank_Signal }

/-- B1: every non-projected, non-bookkeeping register field is unchanged from `r` to `r'`. -/
def NonProjRegsEq (bk : BkKeys) (r r' : Regs) : Prop := mask bk r' = mask bk r

theorem NonProjRegsEq.refl (bk : BkKeys) (r : Regs) : NonProjRegsEq bk r r := rfl
theorem NonProjRegsEq.trans {bk : BkKeys} {r r' r'' : Regs}
    (h₁ : NonProjRegsEq bk r r') (h₂ : NonProjRegsEq bk r' r'') : NonProjRegsEq bk r r'' :=
  Eq.trans h₂ h₁

/-- Example projection of B1: the whole SVE/SME state and DIT are covered. -/
theorem NonProjRegsEq.z {bk : BkKeys} {r r' : Regs} (h : NonProjRegsEq bk r r') : r'._Z = r._Z := by
  have := congrArg Regs._Z h; simpa [mask] using this
theorem NonProjRegsEq.dit {bk : BkKeys} {r r' : Regs} (h : NonProjRegsEq bk r r') :
    r'.PSTATE.DIT = r.PSTATE.DIT := by
  have := congrArg (fun x => x.PSTATE.DIT) h; simpa [mask, maskPSTATE] using this
theorem NonProjRegsEq.bank64 {bk : BkKeys} {r r' : Regs} (h : NonProjRegsEq bk r r')
    (k : Bank_BitVec_64) (hk : bk.b64 k = false) : r'.bank_BitVec_64 k = r.bank_BitVec_64 k := by
  have := congrFun (congrArg Regs.bank_BitVec_64 h) k; simpa [mask, maskBank, hk] using this

end ArmCertCT.CT2

#print axioms ArmCertCT.CT2.NonProjRegsEq.trans
#print axioms ArmCertCT.CT2.NonProjRegsEq.z
#print axioms ArmCertCT.CT2.NonProjRegsEq.dit
#print axioms ArmCertCT.CT2.NonProjRegsEq.bank64

/-! ## B4: bookkeeping is path-determined -/

namespace ArmCertCT.CT2

/-- Keep ONLY the bookkeeping fields (the B4 complement of `mask`'s non-projected part). -/
def keepBk (bk : BkKeys) (r : Regs) : Regs :=
  { (default : Regs) with
    PSTATE := { (default : ProcState) with BTYPE := r.PSTATE.BTYPE },
    __BranchTaken := r.__BranchTaken, Branchtypetaken := r.Branchtypetaken,
    __ThisInstrEnc := r.__ThisInstrEnc, BTypeCompatible := r.BTypeCompatible,
    BTypeNext := r.BTypeNext, ShouldAdvanceSS := r.ShouldAdvanceSS, ShouldAdvanceIT := r.ShouldAdvanceIT,
    PhysicalCount := r.PhysicalCount, PMULastThresholdValue := r.PMULastThresholdValue,
    PMUEventAccumulator := r.PMUEventAccumulator, PMEVCNTSVR_EL1 := r.PMEVCNTSVR_EL1,
    SPESampleCounter := r.SPESampleCounter, SPERecordData := r.SPERecordData,
    __SPE_LFSR := r.__SPE_LFSR, SPESampleOpType := r.SPESampleOpType,
    __emulator_termination_opcode := r.__emulator_termination_opcode,
    bank_BitVec_32 := fun k => if bk.b32 k then r.bank_BitVec_32 k else default,
    bank_Vector_BitVec_32_16 := fun k => if bk.v32_16 k then r.bank_Vector_BitVec_32_16 k else default,
    bank_Vector_BitVec_32_4 := fun k => if bk.v32_4 k then r.bank_Vector_BitVec_32_4 k else default,
    bank_Vector_BitVec_64_32 := fun k => if bk.v64_32 k then r.bank_Vector_BitVec_64_32 k else default,
    bank_BitVec_64 := fun k => if bk.b64 k then r.bank_BitVec_64 k else default,
    bank_Vector_BitVec_64_16 := fun k => if bk.v64_16 k then r.bank_Vector_BitVec_64_16 k else default,
    bank_Vector_BitVec_64_4 := fun k => if bk.v64_4 k then r.bank_Vector_BitVec_64_4 k else default,
    bank_Vector_BitVec_32_31 := fun k => if bk.v32_31 k then r.bank_Vector_BitVec_32_31 k else default,
    bank_Bool := fun k => if bk.bool k then r.bank_Bool k else default,
    bank_Int := fun k => if bk.int k then r.bank_Int k else default,
    bank_BitVec_1 := fun k => if bk.b1 k then r.bank_BitVec_1 k else default,
    bank_BitVec_56 := fun k => if bk.b56 k then r.bank_BitVec_56 k else default,
    bank_BitVec_16 := fun k => if bk.b16 k then r.bank_BitVec_16 k else default,
    bank_BitVec_4 := fun k => if bk.b4 k then r.bank_BitVec_4 k else default,
    bank_BitVec_128 := fun k => if bk.b128 k then r.bank_BitVec_128 k else default,
    bank_Vector_Bool_32 := fun k => if bk.vbool32 k then r.bank_Vector_Bool_32 k else default,
    bank_Vector_BitVec_64_64 := fun k => if bk.v64_64 k then r.bank_Vector_BitVec_64_64 k else default,
    bank_Option_InterruptID := fun k => if bk.irq k then r.bank_Option_InterruptID k else default,
    bank_BitVec_8 := fun k => if bk.b8 k then r.bank_BitVec_8 k else default,
    bank_BitVec_2 := fun k => if bk.b2 k then r.bank_BitVec_2 k else default,
    bank_Vector_BitVec_64_7 := fun k => if bk.v64_7 k then r.bank_Vector_BitVec_64_7 k else default,
    bank_Signal := fun k => if bk.signal k then r.bank_Signal k else default }

/-- B4 per-step conjunct, RELATIONAL (to be stated by alongside NonProjRegsEq, for the actual
model step `step`): two admitted steps from states with the same PC, the same fetched word, equal
bookkeeping, equal masked state and equal choice/cycle bookkeeping of the carrier end with equal
bookkeeping and equal choice/cycle bookkeeping. Gives "bookkeeping equal across two runs on the same
public word sequence" by induction (both runs are SecretVariant-equal at entry). -/
def BkStepDet {S : Type} (bk : BkKeys) (regs : S → Regs) (carrierBk : S → S → Prop)
    (step : S → Option S) (admitted : S → Prop) (pc : S → BitVec 64) (word : S → BitVec 32) : Prop :=
  ∀ s t s' t', admitted s → admitted t → step s = some s' → step t = some t' →
    pc s = pc t → word s = word t →
    keepBk bk (regs s) = keepBk bk (regs t) → mask bk (regs s) = mask bk (regs t) → carrierBk s t →
    keepBk bk (regs s') = keepBk bk (regs t') ∧ carrierBk s' t'

end ArmCertCT.CT2
