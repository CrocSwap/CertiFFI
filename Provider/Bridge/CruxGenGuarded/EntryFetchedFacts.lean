import Bridge.CruxGenGuarded.EntryActualFetch
import Bridge.CruxGenGuarded.EntryBeforeFetch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! Current-state facts at the ACTUAL fetched state of `entry_fetch_current`:
its registers are `fetchGuardRegs acc next (fetchRegs (beforeFetchState s).regs)`
(the fetch wrapper's own BTypeCompatible/__InstructionStep writes and the actual
walk's SetInGuardedPage for the actual descriptor). These are derived, not
supplied by the caller; they feed the fixed-class `native_tail` theorems. -/

abbrev FetchedRegs (acc : AccessDescriptor) (next : TTWState) (s : NativeState) : Regs :=
  fetchGuardRegs acc next (ArmCert.Eval.M1a.Fetch2.fetchRegs (ArmBridge.CruxGenGuarded.beforeFetchState s).regs)

theorem fetched_bool (acc : AccessDescriptor) (next : TTWState) (r : Regs) (k : Bank_Bool)
    (h1 : k ≠ .InGuardedPage) (h2 : k ≠ .__InstructionStep) :
    (fetchGuardRegs acc next (ArmCert.Eval.M1a.Fetch2.fetchRegs r)).bank_Bool k = r.bank_Bool k := by
  unfold fetchGuardRegs
  split
  · simp (disch := first | exact h1 | exact h2 | decide) only [gpRegs, ArmCert.Eval.M1a.Fetch2.fetchRegs,
      Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne]
  · simp (disch := first | exact h1 | exact h2 | decide) only [ArmCert.Eval.M1a.Fetch2.fetchRegs,
      Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne]

run_cmd do
  IO.eprintln "CURRENT_DECL EntryFetchedFacts.fetched_pins"
  (← IO.getStderr).flush

theorem fetched_pins (acc : AccessDescriptor) (next : TTWState) (s t : NativeState)
    (hp : NativeEntryTail.EntryPins s) (hregs : t.regs = FetchedRegs acc next s) :
    NativeEntryTail.EntryPins t := by
  have u := entry_before_fetch_pins s hp
  have spe : t.regs.bank_Bool .SPESampleInFlight = false := by
    rw [hregs, FetchedRegs, fetched_bool _ _ _ _ (by decide) (by decide)]; exact u.spe
  constructor
  all_goals first
    | exact spe
    | (rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> first | exact u.f4 | exact u.rme | exact u.el | exact u.nrw | exact u.edecr | exact u.cti | exact u.st | exact u.edesr | exact u.btt | exact u.emu | exact u.e2h | exact u.tge | exact u.scrns | exact u.pmbe | exact u.mdss | exact u.pmbs | exact u.da | exact u.di | exact u.df | exact u.il | exact u.pss)

run_cmd do
  IO.eprintln "CURRENT_DECL EntryFetchedFacts.fetched_rest"
  (← IO.getStderr).flush

theorem fetched_rest (acc : AccessDescriptor) (next : TTWState) (s t : NativeState) (ticks : Nat)
    (hp : NativeEntryTail.EntryPins s) (q : HookQuiet ticks s)
    (hregs : t.regs = FetchedRegs acc next s) :
    MetadataGuard t ∧ HookQuiet ticks t ∧
    t.regs.ShouldAdvanceIT = false ∧ t.regs.ShouldAdvanceSS = true := by
  have p := fetched_pins acc next s t hp hregs
  have g := entry_before_fetch_metadata s hp
  have qu := entry_before_fetch_quiet s ticks q
  have raw := entry_before_fetch_raw s
  refine ⟨⟨p.f4, p.rme, p.el, p.nrw, p.e2h, p.tge, p.scrns, p.pmbe, p.st, ?_⟩, ?_, ?_, ?_⟩
  · rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> exact g.see
  · apply quiet_of_fields ticks _ t qu
    have spe : t.regs.bank_Bool .SPESampleInFlight =
        (ArmBridge.CruxGenGuarded.beforeFetchState s).regs.bank_Bool .SPESampleInFlight := by
      rw [hregs, FetchedRegs, fetched_bool _ _ _ _ (by decide) (by decide)]
    refine ⟨?_, ?_, ?_, spe, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl)
      | (intro k _; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl)
  · rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> exact raw.2.2.1
  · rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> exact raw.2.2.2

run_cmd do
  IO.eprintln "CURRENT_DECL EntryFetchedFacts.fetched_input"
  (← IO.getStderr).flush

theorem fetched_mask (acc : AccessDescriptor) (next : TTWState) (s : NativeState) :
    ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap (FetchedRegs acc next s) =
      ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap (ArmBridge.CruxGenGuarded.beforeFetchState s).regs := by
  unfold FetchedRegs fetchGuardRegs
  split <;>
    simp (disch := decide) only [ArmCertCT.CT2.mask, gpRegs, ArmCert.Eval.M1a.Fetch2.fetchRegs,
      Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool,
      ArmBridge.CruxNonProj.maskBank_set]

theorem fetched_input (acc : AccessDescriptor) (next : TTWState) (s t : NativeState)
    (el : s.regs.PSTATE.EL = 0#2) (hregs : t.regs = FetchedRegs acc next s) :
    NativeEntryInput.Input s t := by
  have i := entry_before_fetch_input s el
  have nonProj : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap s.regs t.regs := by
    have h := i.controls.nonProj
    unfold ArmCertCT.CT2.NonProjRegsEq at h ⊢
    rw [hregs, fetched_mask]; exact h
  refine ⟨?gpr, ?sp, ?z, ?ps, ?sys, ?spx1, ?spx2, ?spx3, el, ?pc, ⟨nonProj, ?btn⟩⟩
  case gpr => rw [hregs]; refine i.gpr.trans ?_; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case sp => rw [hregs]; refine i.sp.trans ?_; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case z => rw [hregs]; refine i.z.trans ?_; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case ps => rw [hregs]; refine i.ps.trans ?_; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case spx1 => rw [hregs]; refine i.spx1.trans ?_; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case spx2 => rw [hregs]; refine i.spx2.trans ?_; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case spx3 => rw [hregs]; refine i.spx3.trans ?_; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case pc => rw [hregs]; refine Eq.trans ?_ i.pc; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case btn => rw [hregs]; refine Eq.trans ?_ i.controls.btn; unfold FetchedRegs fetchGuardRegs; split <;> rfl
  case sys =>
    have e := i.sys
    refine ⟨?feat, ?el, ?nrw, ?sctlr, ?tcr, ?tcr2, ?hcr, ?scr, ?mair, ?mdscr, ?httbr, ?ttbr0, ?ttbr1, ?hde, ?tlb, ?spe, ?pa⟩
    case feat => refine e.feat.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case el => refine e.el.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case nrw => refine e.nrw.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case sctlr => refine e.sctlr.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case tcr => refine e.tcr.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case tcr2 => refine e.tcr2.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case hcr => refine e.hcr.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case scr => refine e.scr.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case mair => refine e.mair.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case mdscr => refine e.mdscr.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case httbr => refine e.httbr.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case ttbr0 => refine e.ttbr0.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case ttbr1 => refine e.ttbr1.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case hde => refine e.hde.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case pa => refine e.pa.trans ?_; rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl
    case tlb => refine e.tlb.trans ?_; rw [hregs, FetchedRegs, fetched_bool _ _ _ _ (by decide) (by decide)]
    case spe => refine e.spe.trans ?_; rw [hregs, FetchedRegs, fetched_bool _ _ _ _ (by decide) (by decide)]

#print axioms fetched_bool
#print axioms fetched_rest
#print axioms fetched_mask
#print axioms fetched_input
#print axioms fetched_pins
end ArmBridge.CruxGenGuarded.EntryFetchedFacts
