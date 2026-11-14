import ReleaseProfile.GB10.CallerDomain
import ArmCert.HookQuiet.V0.Predicate

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024

/-!
# GB10 canonical source: admissible domain and the only configuration constructor

`SourceDomain` is the D248/D250 worked-design source domain (worked-normal-ct-v2 DEFINITIONS.txt):
coverage, declared values, encoder typing, the physical PA projection, the ratified ControlRows control
bit equations and feature/bank alias agreement. Coverage, typing and declared values hold by
construction of `canonicalSource`; the remaining fields are proved for every completion below.
SourceRestrictions holds the named Doug restrictions (D252 TCR2 guard, D252-A TRM PMU option set,
D252-C EntryQuiescence); they are applied identically to C1 and C2 and enter the premise manifest.

The three D245-scoped bits (SCTLR_EL2.WXN, TCR_EL2.IPS, raw TCR_EL2.T0SZ) are NOT in the domain:
they remain typed unresolved symbols `PENDING:<premise>` pending Doug's scoped signature.
Ratified ControlRows bits carry an external deployment-obligation key; nothing here is a readback.

`Configuration` is indexed by an admissible completion and an admissible caller. Its constructor
is private to this module, so no valid-profile use can bypass the domain proofs.
-/

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

namespace HQ
export ArmCert.HookQuiet.V0 (reg64 feature physical el2Enabled effectiveNS realm physicalOffset)
end HQ

/-- A 64-bit register word as interpreted by the canonical source. Entry-data keys (the HTTBR page-table-root
alias, boss c2d2; the generic timers, boss 820e) are not source coordinates; they read as 0 here and are never
used as configuration. -/
def controlWord (unknowns : Unknowns) (caller : Caller) (key : ArmFull.Bank_BitVec_64) :
    BitVec 64 :=
  if h : isEntryData64 key = true then 0#64
  else interpret unknowns caller ⟨.bank_BitVec_64 key, bank64_notData key (Bool.eq_false_iff.mpr h)⟩

theorem controlWord_eq (unknowns : Unknowns) (caller : Caller) (key : ArmFull.Bank_BitVec_64)
    (h : isEntryData64 key = false) :
    controlWord unknowns caller key = interpret unknowns caller ⟨.bank_BitVec_64 key, bank64_notData key h⟩ :=
  dif_neg (by simp [h])

theorem controlWord_entry (unknowns : Unknowns) (caller : Caller) (key : ArmFull.Bank_BitVec_64)
    (h : isEntryData64 key = true) : controlWord unknowns caller key = 0#64 :=
  dif_pos h

def controlWord32 (unknowns : Unknowns) (caller : Caller) (key : ArmFull.Bank_BitVec_32) :
    BitVec 32 :=
  interpret unknowns caller ⟨.bank_BitVec_32 key, rfl⟩

#check "CURRENT_DECL GB10.ConstructionFacts"
/-- Worked-design domain equations that the canonical source discharges for EVERY completion:
coverage/typing/declared values by construction, PA bits, every declared control bit (ControlRows/D252),
TRM implementation constants and feature/bank alias agreement. -/
structure ConstructionFacts (unknowns : Unknowns) : Prop where
  pa_bits : ∀ caller : Caller,
    interpret unknowns caller ⟨.bank_Int .__supported_pa_size, rfl⟩ = (40 : Int)
  control64 : ∀ (caller : Caller) (key : ArmFull.Bank_BitVec_64) (index : Fin 64) (value : Bool)
    (authority : AuthorityRef), isControlWord key = true →
    controlDeclared key index.val = some (value, authority) →
    (controlWord unknowns caller key).getLsbD index.val = value
  control32 : ∀ (caller : Caller) (key : ArmFull.Bank_BitVec_32) (index : Fin 32) (value : Bool)
    (authority : AuthorityRef), isControlWord32 key = true →
    controlDeclared32 key index.val = some (value, authority) →
    (controlWord32 unknowns caller key).getLsbD index.val = value
  breakpoints : ∀ caller : Caller,
    interpret unknowns caller ⟨.bank_Int .NUM_BREAKPOINTS, rfl⟩ = (6 : Int)
  watchpoints : ∀ caller : Caller,
    interpret unknowns caller ⟨.bank_Int .NUM_WATCHPOINTS, rfl⟩ = (4 : Int)
  contextBreakpoints : ∀ caller : Caller,
    interpret unknowns caller ⟨.bank_Int .__num_ctx_breakpoints, rfl⟩ = (2 : Int)
  feature_bank : ∀ (caller : Caller) (bank : ArmFull.Bank_Bool) (index : Fin 259),
    FeatureSource.bankAlias bank = some index →
      interpret unknowns caller ⟨.bank_Bool bank, rfl⟩ =
        interpret unknowns caller ⟨.feature index, rfl⟩

theorem constructionFacts_holds (unknowns : Unknowns) : ConstructionFacts unknowns where
  pa_bits caller := interpret_pa_bits unknowns caller
  control64 caller key index value authority control record := by
    rw [controlWord_eq unknowns caller key (control_notEntry control)]
    exact interpret_control_declared unknowns caller key control (coordinates_control key control) index
      value authority record
  control32 caller key index value authority control record :=
    interpret_control32_declared unknowns caller key control (coordinates_control32 key control) index
      value authority record
  breakpoints caller := interpret_trm_NUM_BREAKPOINTS unknowns caller
  watchpoints caller := interpret_trm_NUM_WATCHPOINTS unknowns caller
  contextBreakpoints caller := interpret_trm___num_ctx_breakpoints unknowns caller
  feature_bank caller bank index alias :=
    (interpret_feature_bank unknowns caller bank index alias).trans
      (interpret_feature unknowns caller index).symm

#check "CURRENT_DECL GB10.EntryQuiescence"
/-- GB10.EntryQuiescence (D252-C): exact leaves of the entry model/debug state, at ENTRY.
Scope: the actual invocation entry epoch; covered by the bounded OS premise. -/
structure EntryQuiescence (regs : ArmFull.Regs) : Prop where
  /-- original: e.regs.bank_Bool SPESampleInFlight = false (ENTRY; normal 23/107/190/212) -/
  speIdle : regs.bank_Bool .SPESampleInFlight = false
  /-- original: e.regs.Branchtypetaken ≠ BranchType_RESET (ENTRY; normal 30) -/
  notReset : regs.Branchtypetaken ≠ .BranchType_RESET
  /-- original: e.regs.__emulator_termination_opcode = none (ENTRY; normal 31) -/
  noEmulatorStop : regs.__emulator_termination_opcode = none
  /-- original: e.regs.BTypeNext = 0#2 (ENTRY; normal 44) -/
  btypeNext : regs.BTypeNext = 0#2
  /-- original: (beforeFetchState e).regs.bank_Bool __tlb_enabled = false (BEFORE_FETCH; normal 101);
  beforeFetchState leaves bank_Bool unchanged. -/
  tlbModelOff : regs.bank_Bool .__tlb_enabled = false
  /-- original: e.regs.bank_Option_InterruptID __GIC_Pending = none (ENTRY; normal 120) -/
  gicIdle : regs.bank_Option_InterruptID .__GIC_Pending = none
  /-- original: _get_EDSCR_Type_STATUS (e.regs._EDSCR) = 2#6, getter = extractLsb 5 0 (ENTRY; 28/189);
  architectural debug status -/
  edscrStatus : Sail.BitVec.extractLsb (regs.bank_BitVec_32 ._EDSCR) 5 0 = 2#6
  /-- original: e.regs.bank_BitVec_32 EDESR = 0#32 (ENTRY; normal 29); architectural debug status -/
  edesrClear : regs.bank_BitVec_32 .EDESR = 0#32
  /-- original: _get_EDESR_Type_OSUC (e.regs.EDESR) = 0#1, getter = extractLsb 0 0 (ENTRY; normal 200) -/
  edesrOsuc : Sail.BitVec.extractLsb (regs.bank_BitVec_32 .EDESR) 0 0 = 0#1
  /-- original: extractLsb (e.regs.PMBSR_EL1) 17 17 = 0#1 (ENTRY; normal 37); architectural status -/
  pmbsrS : Sail.BitVec.extractLsb (regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1

/-- The exact EntryQuiescence leaves on the canonical interpretation of the same coordinates. -/
structure EntryQuiescenceSource (unknowns : Unknowns) (caller : Caller) : Prop where
  speIdle : interpret unknowns caller ⟨.bank_Bool .SPESampleInFlight, rfl⟩ = false
  notReset : interpret unknowns caller ⟨.Branchtypetaken, rfl⟩ ≠ ArmFull.BranchType.BranchType_RESET
  noEmulatorStop : interpret unknowns caller ⟨.__emulator_termination_opcode, rfl⟩ = (none : Option (BitVec 32))
  btypeNext : interpret unknowns caller ⟨.BTypeNext, rfl⟩ = (0#2 : BitVec 2)
  tlbModelOff : interpret unknowns caller ⟨.bank_Bool .__tlb_enabled, rfl⟩ = false
  gicIdle : interpret unknowns caller ⟨.bank_Option_InterruptID .__GIC_Pending, rfl⟩ =
    (none : Option ArmFull.InterruptID)
  edscrStatus : Sail.BitVec.extractLsb (controlWord32 unknowns caller ._EDSCR) 5 0 = 2#6
  edesrClear : controlWord32 unknowns caller .EDESR = 0#32
  edesrOsuc : Sail.BitVec.extractLsb (controlWord32 unknowns caller .EDESR) 0 0 = 0#1
  pmbsrS : Sail.BitVec.extractLsb (controlWord unknowns caller .PMBSR_EL1) 17 17 = 0#1

/-- Any register file agreeing with the source at every profile coordinate is quiescent. -/
theorem entryQuiescence_of_agreement {unknowns : Unknowns} {caller : Caller}
    (source : EntryQuiescenceSource unknowns caller) (regs : ArmFull.Regs)
    (agree : ∀ c : ProfileCoordinate, RawCoordinate.read regs c.val = interpret unknowns caller c) :
    EntryQuiescence regs where
  speIdle := (agree ⟨.bank_Bool .SPESampleInFlight, rfl⟩).trans source.speIdle
  notReset := fun same => source.notReset ((agree ⟨.Branchtypetaken, rfl⟩).symm.trans same)
  noEmulatorStop := (agree ⟨.__emulator_termination_opcode, rfl⟩).trans source.noEmulatorStop
  btypeNext := (agree ⟨.BTypeNext, rfl⟩).trans source.btypeNext
  tlbModelOff := (agree ⟨.bank_Bool .__tlb_enabled, rfl⟩).trans source.tlbModelOff
  gicIdle := (agree ⟨.bank_Option_InterruptID .__GIC_Pending, rfl⟩).trans source.gicIdle
  edscrStatus := by
    rw [show regs.bank_BitVec_32 ._EDSCR = _ from agree ⟨.bank_BitVec_32 ._EDSCR, rfl⟩]
    exact source.edscrStatus
  edesrClear := (agree ⟨.bank_BitVec_32 .EDESR, rfl⟩).trans source.edesrClear
  edesrOsuc := by
    rw [show regs.bank_BitVec_32 .EDESR = _ from agree ⟨.bank_BitVec_32 .EDESR, rfl⟩]
    exact source.edesrOsuc
  pmbsrS := by
    rw [show regs.bank_BitVec_64 .PMBSR_EL1 = _ from agree ⟨.bank_BitVec_64 .PMBSR_EL1, rfl⟩]
    exact source.pmbsrS

#check "CURRENT_DECL GB10.TimersQuiet"
/-- GB10.TimersQuiet (D264): the seven exact original timer atoms at ENTRY, for `budget` future
counter updates. Entry environment state (PhysicalCount is data, budget is program data), not
configuration; a named scoped premise identical in C1 and C2, covered by the bounded OS premise. -/
structure TimersQuiet (regs : ArmFull.Regs) (budget : Nat) : Prop where
  /-- original normal 113, CT 114/364 (ENTRY; guard, ENABLE, IMASK, forced mask, deadline):
  card:default-initial/v1/quiet/timers/cntp -/
  cntp : true = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTP_CTL_EL0).getLsbD 0 = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTP_CTL_EL0).getLsbD 1 = true ∨ (HQ.realm regs && ArmFull.Functions._get_CNTHCTL_EL2_Type_CNTPMASK (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHCTL_EL2) == 1#1) = true ∨ (HQ.physicalOffset regs).toNat ≤ HQ.physical regs ∧ HQ.physical regs + budget < 2 ^ 64 ∧ HQ.physical regs + budget - (HQ.physicalOffset regs).toNat < (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTP_CVAL_EL0).toNat
  /-- original normal 114, CT 115/365 (ENTRY; guard, ENABLE, IMASK, forced mask, deadline):
  card:default-initial/v1/quiet/timers/cnthp -/
  cnthp : true = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHP_CTL_EL2).getLsbD 0 = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHP_CTL_EL2).getLsbD 1 = true ∨ false = true ∨ (0#64).toNat ≤ HQ.physical regs ∧ HQ.physical regs + budget < 2 ^ 64 ∧ HQ.physical regs + budget - (0#64).toNat < (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHP_CVAL_EL2).toNat
  /-- original normal 115, CT 116/366 (ENTRY; guard, ENABLE, IMASK, forced mask, deadline):
  card:default-initial/v1/quiet/timers/cnthps -/
  cnthps : HQ.feature regs ArmFull.Feature.FEAT_SEL2 = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHPS_CTL_EL2).getLsbD 0 = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHPS_CTL_EL2).getLsbD 1 = true ∨ false = true ∨ (0#64).toNat ≤ HQ.physical regs ∧ HQ.physical regs + budget < 2 ^ 64 ∧ HQ.physical regs + budget - (0#64).toNat < (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHPS_CVAL_EL2).toNat
  /-- original normal 116, CT 117/367 (ENTRY; guard, ENABLE, IMASK, forced mask, deadline):
  card:default-initial/v1/quiet/timers/cntps -/
  cntps : true = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTPS_CTL_EL1).getLsbD 0 = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTPS_CTL_EL1).getLsbD 1 = true ∨ false = true ∨ (HQ.physicalOffset regs).toNat ≤ HQ.physical regs ∧ HQ.physical regs + budget < 2 ^ 64 ∧ HQ.physical regs + budget - (HQ.physicalOffset regs).toNat < (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTPS_CVAL_EL1).toNat
  /-- original normal 117, CT 118/368 (ENTRY; guard, ENABLE, IMASK, forced mask, deadline):
  card:default-initial/v1/quiet/timers/cntv -/
  cntv : true = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTV_CTL_EL0).getLsbD 0 = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTV_CTL_EL0).getLsbD 1 = true ∨ (HQ.realm regs && ArmFull.Functions._get_CNTHCTL_EL2_Type_CNTVMASK (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHCTL_EL2) == 1#1) = true ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTVOFF_EL2).toNat ≤ HQ.physical regs ∧ HQ.physical regs + budget < 2 ^ 64 ∧ HQ.physical regs + budget - (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTVOFF_EL2).toNat < (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTV_CVAL_EL0).toNat
  /-- original normal 118, CT 119/369 (ENTRY; guard, ENABLE, IMASK, forced mask, deadline):
  card:default-initial/v1/quiet/timers/cnthv -/
  cnthv : HQ.feature regs ArmFull.Feature.FEAT_VHE = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHV_CTL_EL2).getLsbD 0 = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHV_CTL_EL2).getLsbD 1 = true ∨ false = true ∨ (0#64).toNat ≤ HQ.physical regs ∧ HQ.physical regs + budget < 2 ^ 64 ∧ HQ.physical regs + budget - (0#64).toNat < (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHV_CVAL_EL2).toNat
  /-- original normal 119, CT 120/370 (ENTRY; guard, ENABLE, IMASK, forced mask, deadline):
  card:default-initial/v1/quiet/timers/cnthvs -/
  cnthvs : (HQ.feature regs ArmFull.Feature.FEAT_SEL2 && HQ.feature regs ArmFull.Feature.FEAT_VHE) = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHVS_CTL_EL2).getLsbD 0 = false ∨ (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHVS_CTL_EL2).getLsbD 1 = true ∨ false = true ∨ (0#64).toNat ≤ HQ.physical regs ∧ HQ.physical regs + budget < 2 ^ 64 ∧ HQ.physical regs + budget - (0#64).toNat < (HQ.reg64 regs ArmFull.Bank_BitVec_64.CNTHVS_CVAL_EL2).toNat

private theorem deadline_mono {o p c budget small : Nat} (h : small ≤ budget) :
    o ≤ p ∧ p + budget < 2 ^ 64 ∧ p + budget - o < c → o ≤ p ∧ p + small < 2 ^ 64 ∧ p + small - o < c :=
  fun ⟨a, b, d⟩ => ⟨a, Nat.lt_of_le_of_lt (Nat.add_le_add_left h _) b,
    Nat.lt_of_le_of_lt (Nat.sub_le_sub_right (Nat.add_le_add_left h _) _) d⟩

/-- TimersQuiet is monotone downward in the budget. -/
theorem TimersQuiet.mono {regs : ArmFull.Regs} {budget small : Nat} (t : TimersQuiet regs budget)
    (h : small ≤ budget) : TimersQuiet regs small where
  cntp := t.cntp.imp_right (Or.imp_right (Or.imp_right (Or.imp_right (deadline_mono h))))
  cnthp := t.cnthp.imp_right (Or.imp_right (Or.imp_right (Or.imp_right (deadline_mono h))))
  cnthps := t.cnthps.imp_right (Or.imp_right (Or.imp_right (Or.imp_right (deadline_mono h))))
  cntps := t.cntps.imp_right (Or.imp_right (Or.imp_right (Or.imp_right (deadline_mono h))))
  cntv := t.cntv.imp_right (Or.imp_right (Or.imp_right (Or.imp_right (deadline_mono h))))
  cnthv := t.cnthv.imp_right (Or.imp_right (Or.imp_right (Or.imp_right (deadline_mono h))))
  cnthvs := t.cnthvs.imp_right (Or.imp_right (Or.imp_right (Or.imp_right (deadline_mono h))))

/-- TimersQuiet reads only the 64-bit bank, the feature vector and PhysicalCount. -/
theorem TimersQuiet.congr {regs other : ArmFull.Regs} {budget : Nat} (t : TimersQuiet regs budget)
    (bank : ∀ key, regs.bank_BitVec_64 key = other.bank_BitVec_64 key)
    (features : regs.FeatureImpl = other.FeatureImpl)
    (count : regs.PhysicalCount = other.PhysicalCount) : TimersQuiet other budget := by
  have e1 : ∀ k, HQ.reg64 regs k = HQ.reg64 other k := bank
  have e2 : ∀ f, HQ.feature regs f = HQ.feature other f := fun f => by simp only [HQ.feature, features]
  have e3 : HQ.physical regs = HQ.physical other := by simp only [HQ.physical, count]
  have e4 : HQ.realm regs = HQ.realm other := by
    simp only [HQ.realm, HQ.effectiveNS, e1 .SCR_EL3, e2]
  have e5 : HQ.physicalOffset regs = HQ.physicalOffset other := by
    unfold HQ.physicalOffset HQ.el2Enabled
    rw [e1 .CNTHCTL_EL2, e1 .SCR_EL3, e1 .CNTPOFF_EL2, e2 .FEAT_ECV, e2 .FEAT_SEL2]
  obtain ⟨cntp, cnthp, cnthps, cntps, cntv, cnthv, cnthvs⟩ := t
  simp only [e1, e2, e3, e4, e5] at cntp cnthp cnthps cntps cntv cnthv cnthvs
  exact ⟨cntp, cnthp, cnthps, cntps, cntv, cnthv, cnthvs⟩

#check "CURRENT_DECL GB10.timersBudget"
/-- Largest card budget in scope (Heap 369 = 357 + 12; Runtime14 plans <= 22). Kept for card statements;
quiet-by-construction holds for every budget. -/
def timersBudget : Nat := 369

#check "CURRENT_DECL GB10.timerCtlKeys"
/-- The seven generic timers' CTL registers (entry data, boss 820e). -/
def timerCtlKeys : List ArmFull.Bank_BitVec_64 :=
  [.CNTP_CTL_EL0, .CNTHP_CTL_EL2, .CNTHPS_CTL_EL2, .CNTPS_CTL_EL1, .CNTV_CTL_EL0, .CNTHV_CTL_EL2, .CNTHVS_CTL_EL2]

#check "CURRENT_DECL GB10.TimersDisabled"
/-- Every generic timer is disabled (CTL.ENABLE = 0) in a 64-bit bank. The positive C2 payload's timer data is
chosen so; this is a property of entry data, not configuration. -/
def TimersDisabled (bank : ArmFull.Bank_BitVec_64 → BitVec 64) : Prop :=
  ∀ key ∈ timerCtlKeys, (bank key).getLsbD 0 = false

#check "CURRENT_DECL GB10.timersQuiet_of_disabled"
/-- Quiet by construction: disabled timers satisfy every GB10.TimersQuiet atom (the ENABLE disjunct), for
every budget. -/
theorem timersQuiet_of_disabled (regs : ArmFull.Regs) (h : TimersDisabled regs.bank_BitVec_64)
    (budget : Nat) : TimersQuiet regs budget where
  cntp := Or.inr (Or.inl (h .CNTP_CTL_EL0 (by decide)))
  cnthp := Or.inr (Or.inl (h .CNTHP_CTL_EL2 (by decide)))
  cnthps := Or.inr (Or.inl (h .CNTHPS_CTL_EL2 (by decide)))
  cntps := Or.inr (Or.inl (h .CNTPS_CTL_EL1 (by decide)))
  cntv := Or.inr (Or.inl (h .CNTV_CTL_EL0 (by decide)))
  cnthv := Or.inr (Or.inl (h .CNTHV_CTL_EL2 (by decide)))
  cnthvs := Or.inr (Or.inl (h .CNTHVS_CTL_EL2 (by decide)))

#check "CURRENT_DECL GB10.SourceRestrictions"
/-- Named restrictions of the completion domain, applied identically to C1 and positive C2 and
listed in the premise manifest. Each is a Doug decision; none is a convenient completion. -/
structure SourceRestrictions (unknowns : Unknowns) : Prop where
  /-- D252: TCR2_EL2 D128/AIE/PnCH are 0 whenever FEAT_TCR2 (feature 178) is implemented. -/
  tcr2Guard : ∀ caller : Caller, FeatureSource.value unknowns.features 178 = true →
    (interpret unknowns caller ⟨.bank_BitVec_64 .TCR2_EL2, rfl⟩).getLsbD 5 = false ∧
    (interpret unknowns caller ⟨.bank_BitVec_64 .TCR2_EL2, rfl⟩).getLsbD 4 = false ∧
    (interpret unknowns caller ⟨.bank_BitVec_64 .TCR2_EL2, rfl⟩).getLsbD 0 = false
  /-- D252-A TRM grade, per core kind: PMU event counters are a build option
  (X925 6|31: x925.txt:1308-1309; A725 6|20: a725.txt:1151-1152). No value is chosen. -/
  pmuCountersTrm : ∀ caller : Caller,
    match unknowns.coreKind with
    | .x925 => interpret unknowns caller ⟨.bank_Int .NUM_PMU_COUNTERS, rfl⟩ = (6 : Int) ∨
        interpret unknowns caller ⟨.bank_Int .NUM_PMU_COUNTERS, rfl⟩ = (31 : Int)
    | .a725 => interpret unknowns caller ⟨.bank_Int .NUM_PMU_COUNTERS, rfl⟩ = (6 : Int) ∨
        interpret unknowns caller ⟨.bank_Int .NUM_PMU_COUNTERS, rfl⟩ = (20 : Int)
  /-- D252-C GB10.EntryQuiescence, stated on the source view of the entry coordinates. -/
  entryQuiescence : ∀ caller : Caller, EntryQuiescenceSource unknowns caller

#check "CURRENT_DECL GB10.SourceDomain"
/-- Exact worked-design source domain: construction facts plus the named restrictions.
No outcome, CurrentInv, MathInputs or success predicate. -/
structure SourceDomain (unknowns : Unknowns) : Prop where
  construction : ConstructionFacts unknowns
  restrictions : SourceRestrictions unknowns

#check "CURRENT_DECL GB10.AdmissibleSourceCompletion"
/-- The same completion domain is bound by C1, positive C2 and admission. -/
abbrev AdmissibleSourceCompletion := { unknowns : Unknowns // SourceDomain unknowns }

/-- Caller entry parameters admitted for a completion: exactly the nine worked equations. -/
structure AdmissibleCaller (rho : AdmissibleSourceCompletion) where
  caller : Caller
  normal : NormalCallerDomain caller

/-- CT: two independent admitted callers with explicit equality of their common source views. -/
structure AdmissibleCTCallers (rho : AdmissibleSourceCompletion) where
  first : AdmissibleCaller rho
  second : AdmissibleCaller rho
  context : commonView rho.val first.caller = commonView rho.val second.caller

def AdmissibleCTCallers.ofCallers {rho : AdmissibleSourceCompletion}
    (first second : AdmissibleCaller rho) : AdmissibleCTCallers rho :=
  ⟨first, second, commonView_exact rho.val first.caller second.caller⟩

theorem AdmissibleCTCallers.domain {rho : AdmissibleSourceCompletion}
    (callers : AdmissibleCTCallers rho) :
    CTCallerDomain rho.val callers.first.caller callers.second.caller :=
  ⟨callers.first.normal, callers.second.normal, callers.context⟩

#check "CURRENT_DECL GB10.Configuration"
/-- The only configuration object. Kernel equality binds the complete represented profile to the
fixed source, an admissible completion and an admissible caller; the constructor is private. -/
structure Configuration (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) where
  private mk ::
  values : (c : ProfileCoordinate) → RawCoordinate.Value c.val
  canonical : values = interpret rho.val caller.caller

namespace Configuration

variable {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}

def ofSource (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    Configuration rho caller :=
  ⟨interpret rho.val caller.caller, rfl⟩

theorem coordinate_exact (configuration : Configuration rho caller) (c : ProfileCoordinate) :
    configuration.values c = interpret rho.val caller.caller c :=
  congrFun configuration.canonical c

theorem configuration_exact (configuration : Configuration rho caller) :
    configuration = ofSource rho caller := by
  cases configuration
  rename_i values canonical
  unfold ofSource
  congr 1

/-- Every configuration carries the source-domain proof of its completion. -/
theorem domain (_configuration : Configuration rho caller) : SourceDomain rho.val := rho.property

theorem callerDomain (_configuration : Configuration rho caller) :
    NormalCallerDomain caller.caller := caller.normal

end Configuration

/-- Mathematical entry agreement, not physical observation or source authority. -/
def AgreesAt {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    (configuration : Configuration rho caller) (actualRegs : ArmFull.Regs) : Prop :=
  ∀ c : ProfileCoordinate, RawCoordinate.read actualRegs c.val = configuration.values c

theorem actual_coordinate {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    (configuration : Configuration rho caller) (actualRegs : ArmFull.Regs)
    (agreement : AgreesAt configuration actualRegs) (c : ProfileCoordinate) :
    RawCoordinate.read actualRegs c.val = interpret rho.val caller.caller c :=
  (agreement c).trans (Configuration.coordinate_exact configuration c)

/-- An agreeing actual entry exposes each ratified control bit through the source domain. -/
theorem actual_control_word {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    (configuration : Configuration rho caller) (actualRegs : ArmFull.Regs)
    (agreement : AgreesAt configuration actualRegs) (key : ArmFull.Bank_BitVec_64)
    (h : isEntryData64 key = false := by decide) :
    actualRegs.bank_BitVec_64 key = controlWord rho.val caller.caller key :=
  (actual_coordinate configuration actualRegs agreement ⟨.bank_BitVec_64 key, bank64_notData key h⟩).trans
    (controlWord_eq _ _ key h).symm

theorem actual_hcr_e2h {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    (configuration : Configuration rho caller) (actualRegs : ArmFull.Regs)
    (agreement : AgreesAt configuration actualRegs) :
    (actualRegs.bank_BitVec_64 .HCR_EL2).getLsbD 34 = true := by
  rw [actual_control_word configuration actualRegs agreement .HCR_EL2]
  exact rho.property.construction.control64 caller.caller .HCR_EL2 ⟨34, by decide⟩ true _ rfl rfl

/-- At an agreeing actual entry, GB10.EntryQuiescence holds (D252-C restriction of the domain). -/
theorem actual_entryQuiescence {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    (configuration : Configuration rho caller) (actualRegs : ArmFull.Regs)
    (agreement : AgreesAt configuration actualRegs) : EntryQuiescence actualRegs :=
  entryQuiescence_of_agreement (rho.property.restrictions.entryQuiescence caller.caller) actualRegs
    (actual_coordinate configuration actualRegs agreement)

theorem actual_pstate_el {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    (configuration : Configuration rho caller) (actualRegs : ArmFull.Regs)
    (agreement : AgreesAt configuration actualRegs) :
    actualRegs.PSTATE.EL = 0#2 :=
  (actual_coordinate configuration actualRegs agreement ⟨.pstate_EL, rfl⟩).trans caller.normal.el

theorem updateGpr_preserves_agreement {rho : AdmissibleSourceCompletion}
    {caller : AdmissibleCaller rho} (configuration : Configuration rho caller)
    (regs : ArmFull.Regs) (agreement : AgreesAt configuration regs) (gpr : Vector (BitVec 64) 31) :
    AgreesAt configuration (updateGpr regs gpr) := by
  intro c
  exact (updateGpr_frame regs gpr c).trans (agreement c)

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

private def witnessUnknowns : Unknowns where
  features := fun _ _ => false
  registers := fun c _ => witnessRegister c
  controls := fun _ _ _ => false
  controls32 := fun key index _ => witnessControl32 key index
  coreKind := .x925

private theorem witness_edscr (caller : Caller) (index : Fin 32)
    (notDeclared : controlDeclared32 ._EDSCR index.val = none) :
    (controlWord32 witnessUnknowns caller ._EDSCR).getLsbD index.val = (index.val == 1) :=
  interpret_control32_unresolved witnessUnknowns caller ._EDSCR rfl coordinates32__EDSCR index notDeclared

private theorem witness_restrictions : SourceRestrictions witnessUnknowns where
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
      · simpa using witness_edscr caller ⟨0, by decide⟩ rfl
      · simpa using witness_edscr caller ⟨1, by decide⟩ rfl
      · simpa using witness_edscr caller ⟨2, by decide⟩ rfl
      · simpa using witness_edscr caller ⟨3, by decide⟩ rfl
      · simpa using witness_edscr caller ⟨4, by decide⟩ rfl
      · simpa using witness_edscr caller ⟨5, by decide⟩ rfl
    edesrClear := rfl
    edesrOsuc := by
      show Sail.BitVec.extractLsb (0#32 : BitVec 32) 0 0 = 0#1
      decide
    pmbsrS := by
      show Sail.BitVec.extractLsb (0#64 : BitVec 64) 17 17 = 0#1
      decide }

#check "CURRENT_DECL GB10.sourceDomainWitness"
/-- Positive source/caller domain certificate (design SourceDomainWitness): a mathematical
consistency result only. It selects no invocation completion and claims no observation.
Source projection compatibility with the derived run context is NOT yet included. -/
theorem sourceDomainWitness :
    Nonempty AdmissibleSourceCompletion ∧
    (∀ rho : AdmissibleSourceCompletion, Nonempty (AdmissibleCaller rho)) ∧
    (∀ rho : AdmissibleSourceCompletion, Nonempty (AdmissibleCTCallers rho)) ∧
    (∀ (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho),
      ∃ configuration : Configuration rho caller,
        configuration.values = interpret rho.val caller.caller) := by
  refine ⟨⟨⟨witnessUnknowns, ⟨constructionFacts_holds _, witness_restrictions⟩⟩⟩, ?_, ?_, ?_⟩
  · intro rho
    obtain ⟨caller, normal⟩ := normalCallerDomain_nonempty
    exact ⟨⟨caller, normal⟩⟩
  · intro rho
    obtain ⟨caller, normal⟩ := normalCallerDomain_nonempty
    exact ⟨AdmissibleCTCallers.ofCallers ⟨caller, normal⟩ ⟨caller, normal⟩⟩
  · intro rho caller
    exact ⟨Configuration.ofSource rho caller, rfl⟩

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.constructionFacts_holds
#print axioms ReleaseProfile.GB10.entryQuiescence_of_agreement
#print axioms ReleaseProfile.GB10.actual_entryQuiescence
#print axioms ReleaseProfile.GB10.Configuration.coordinate_exact
#print axioms ReleaseProfile.GB10.Configuration.configuration_exact
#print axioms ReleaseProfile.GB10.actual_coordinate
#print axioms ReleaseProfile.GB10.actual_control_word
#print axioms ReleaseProfile.GB10.actual_hcr_e2h
#print axioms ReleaseProfile.GB10.actual_pstate_el
#print axioms ReleaseProfile.GB10.updateGpr_preserves_agreement
#print axioms ReleaseProfile.GB10.AdmissibleCTCallers.domain
#print axioms ReleaseProfile.GB10.sourceDomainWitness
