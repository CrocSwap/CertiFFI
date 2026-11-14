import Walk.S1Normality
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.IF
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-! Callee lemmas for the instruction-fetch (IFETCH) path of S1Translate (EL2&0). -/

/-! ### Permission check for an EL0 instruction fetch.
`AArch64_S1CheckPermissions` takes its IFETCH branch: the fault is a permission fault iff
the overlay denies execution (overlay is off: FEAT_S1POE off makes `S1E0POEnabled` false),
the memory is Device (CONSTRAINED UNPREDICTABLE), or `s1perms.x = 0`. At EL0 with direct
permissions (PIE = 0), `x = ux = NOT (UXN OR UXNTable)` (WXN = 0 leaves it; NS access leaves it).
AP is irrelevant for execute permission. -/
drive_spec permif_native, permif_eq : fun (f : FaultRecord) (w : TTWState) (wp : S1TTWParams)
    (acc : AccessDescriptor) (s : State)
    (hPOE : s.regs.FeatureImpl[210] = false) (hPAN : s.regs.FeatureImpl[51] = false)
    (hpie : wp.pie = 0#1) (hwxn : wp.wxn = 0#1) (hel : acc.el = 0#2)
    (hacc : acc.acctype = .AccessType_IFETCH) (hss : acc.ss = .SS_NonSecure)
    (hmt : w.memattrs.memtype = .MemType_Normal)
    (huxn : w.permissions.uxn = 0#1) (huxt : w.permissions.uxn_table = 0#1) =>
  AArch64_S1CheckPermissions f .Regime_EL20 w wp acc s

theorem permIF (w : TTWState) (wp : S1TTWParams) (acc : AccessDescriptor) (s : State)
    (hPOE : s.regs.FeatureImpl[210] = false) (hPAN : s.regs.FeatureImpl[51] = false)
    (hpie : wp.pie = 0#1) (hwxn : wp.wxn = 0#1) (hel : acc.el = 0#2)
    (hacc : acc.acctype = .AccessType_IFETCH) (hss : acc.ss = .SS_NonSecure)
    (hmt : w.memattrs.memtype = .MemType_Normal)
    (huxn : w.permissions.uxn = 0#1) (huxt : w.permissions.uxn_table = 0#1) :
    ∀ (f' : FaultRecord) t, f'.statuscode = .Fault_None → Frame s t → ∃ fc u,
      AArch64_S1CheckPermissions f' .Regime_EL20 w wp acc t = .ok fc u ∧
        fc.statuscode = .Fault_None ∧ Frame t u := by
  intro f' t hf ht
  rw [permif_eq f' w wp acc t (by rw [ht.1]; exact hPOE) (by rw [ht.1]; exact hPAN)
    hpie hwxn hel hacc hss hmt huxn huxt]
  observe_simp [Frame, permif_native]
  exact ⟨_, _, ⟨rfl, rfl⟩, hf, rfl, rfl, rfl⟩

/-! ### I-cache enable read (EL2&0): a register read, any value. -/
theorem icache (s : State) :
    ∀ t, Frame s t → ∃ b u, AArch64_S1ICacheEnabled .Regime_EL20 t = .ok b u ∧ Frame t u :=
  fun t _ => ⟨_, t, rfl, rfl, rfl, rfl⟩

/-! ### SetInGuardedPage: the only register write on the IFETCH path. -/
/-- The register file with `InGuardedPage` cleared. -/
def clrGP (R : Regs) : Regs := { R with bank_Bool := RegMap.set R.bank_Bool .InGuardedPage false }

theorem setGP (s : State) :
    SetInGuardedPage false s = .ok () { s with regs := clrGP s.regs } := rfl

theorem clrGP_feat (R : Regs) : (clrGP R).FeatureImpl = R.FeatureImpl := rfl
theorem clrGP_idem (R : Regs) : clrGP (clrGP R) = clrGP R := by
  show ({ R with bank_Bool := RegMap.set (RegMap.set R.bank_Bool Bank_Bool.InGuardedPage false) Bank_Bool.InGuardedPage false } : Regs) = _
  rw [RegMap.set_set_same]
  rfl

/-- If `InGuardedPage` is already false, clearing it changes nothing. -/
theorem clrGP_self (R : Regs) (h : R.bank_Bool .InGuardedPage = false) : clrGP R = R := by
  have : RegMap.set R.bank_Bool .InGuardedPage false = R.bank_Bool := by
    funext k
    simp only [RegMap.set]
    split
    · next hk => subst hk; exact h.symm
    · rfl
  unfold clrGP
  rw [this]

#print axioms permIF
#print axioms icache
#print axioms setGP
#print axioms clrGP_idem
#print axioms clrGP_self
end MemM1.IF
