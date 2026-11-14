import MemM1.M1Core
import MemM1.S1TIF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace MemM1.WitnessIF
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-- M1-c (IFETCH): AArch64_TranslateAddress for an instruction fetch in a profile with RME absent,
    given the results of its sub-calls. For IFETCH the model skips the data-side CheckDebug and
    the SPE latency counters, evaluates the (false) RME/GPC test, then runs CheckDebug. The
    final state differs from the CheckDebug result state only in the event log. -/
theorem translateIF (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (R : Regime) (s0 : State) (tsi : TranslationStartInfo) (s1 : State) (ad : AddressDescriptor) (t : State)
    (df : FaultRecord) (t2 : State)
    (hacc : acc.acctype = .AccessType_IFETCH)
    (hreg : TranslationRegime acc.el s = .ok R s0)
    (htsi : AArch64_GetTranslationStartInfo R acc.ss acc va size s0 = .ok tsi s1)
    (hfull : AArch64_FullTranslate va acc aligned
      { s1 with events := s1.events.push (.translationStart tsi) } = .ok ad t)
    (hnf : ad.fault.statuscode = .Fault_None)
    (hrme : HaveRME () t = .ok false t)
    (hdbg : AArch64_CheckDebug va acc size t = .ok df t2) :
    ∃ t3, AArch64_TranslateAddress va acc aligned size s =
        .ok { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 } t3 ∧
      t3.regs = t2.regs ∧ t3.mem = t2.mem := by
  refine ⟨{ t2 with events := t2.events.push (Event.translationEnd
      { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }) }, ?_, rfl, rfl⟩
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hacc1 : (acc.acctype == AccessType.AccessType_IFETCH) = true := by rw [hacc]; rfl
  have hacc2 : (acc.acctype != AccessType.AccessType_IFETCH) = false := by rw [hacc]; rfl
  unfold AArch64_TranslateAddress
  simp only [Bind.bind, EStateM.bind, readReg, PreSail.readReg_apply, hacc1, Bool.true_or, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, start_translation,
    ArmFull.ConcurrencyInterfaceV1.sail_translation_start, PreSail.sail_translation_start, PreSail.logEvent,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  simp only [hreg, htsi]
  simp only [hfull, IsFault, hnf, hnn, Bool.not_false, Bool.true_and, hacc2, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, EStateM.bind, EStateM.pure, hrme, Bool.false_and, hacc1,
    Bool.and_true, hdbg, Bool.true_or, Bool.not_true, end_translation,
    ArmFull.ConcurrencyInterfaceV1.sail_translation_end, PreSail.sail_translation_end, PreSail.logEvent,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
#print axioms translateIF

/-- The EL0 non-secure instruction-fetch access shape (what `CreateAccDescIFetch ()` returns
    at EL0 in Non-secure state; see `MemM1.AccIF`). -/
structure AccIF (acc : AccessDescriptor) : Prop where
  ss : acc.ss = .SS_NonSecure
  el : acc.el = 0#2
  ifetch : acc.acctype = .AccessType_IFETCH
  ls64 : acc.ls64 = false
  tx : acc.transactional = false
  nf : acc.nonfault = false
  ff : acc.firstfault = false

/-- What the walk-parameter fetch and the S1 walk give at VA `va` on states with the
    registers and memory of `s`, for an instruction fetch: as `WitnessV.WalkOKV`, but the leaf
    facts are the execute-side ones (UXN = 0, UXNTable = 0, GP = 0) instead of AP / APTable. -/
def WalkOKIF (acc : AccessDescriptor) (s : State) (va : BitVec 64) (B : BitVec 56) : Prop :=
  ∀ t : State, t.regs = s.regs → t.mem = s.mem → ∃ wp u,
    AArch64_GetS1TTWParams .Regime_EL20 acc.ss va t = .ok wp u ∧ Frame t u ∧
    wp.d128 = 0#1 ∧ wp.pie = 0#1 ∧ wp.ds = 0#1 ∧ wp.tgx = .TGx_4KB ∧ wp.txsz = 16#6 ∧
    wp.wxn = 0#1 ∧ wp.e0pd = 0#1 ∧
    ∀ (f' : FaultRecord) (v : State), f'.statuscode = .Fault_None → v.regs = s.regs → v.mem = s.mem →
      ∃ fw wa w d u',
      AArch64_S1Walk f' wp va .Regime_EL20 acc 64 v = .ok (fw, wa, w, d) u' ∧
      fw.statuscode = .Fault_None ∧ u'.regs = v.regs ∧ u'.mem = v.mem ∧
      d.getLsbD 10 = true ∧ d.getLsbD 51 = false ∧
      w.memattrs.memtype = .MemType_Normal ∧ w.level = 3 ∧ w.contiguous = 0#1 ∧
      w.baseaddress = {paspace := .PAS_NonSecure, address := B} ∧
      w.permissions.uxn = 0#1 ∧ w.permissions.uxn_table = 0#1 ∧ w.guardedpage = 0#1

/-- M1 core, instruction fetch: the actual AArch64_TranslateAddress at a lower-range `va` for an
    EL0 NS IFETCH access. The only register effect is the model's `SetInGuardedPage false`
    (the leaf has GP = 0), so the final registers are `clrGP s.regs`. -/
theorem coreIF (va : BitVec 64) (hva : va.toNat < 2^48) (B : BitVec 56)
    (hB : B &&& 0xfff#56 = 0#56) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (hR : Witness.Regs20 s.regs) (hA : AccIF acc) (hW : WalkOKIF acc s va B) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ t.regs = MemM1.IF.clrGP s.regs ∧ t.mem = s.mem := by
  have regime : ∀ t : State, t.regs = s.regs →
      ∃ u, TranslationRegime acc.el t = .ok .Regime_EL20 u ∧ Frame t u := by
    intro t ht
    rw [hA.el]
    exact MemM1.Callees.regime_el0 t (by rw [ht]; exact hR.noRME) (by rw [ht]; exact hR.vhe)
      (by rw [ht]; exact hR.aa64el0) (by rw [ht]; exact hR.ns) (by rw [ht]; exact hR.e2h)
      (by rw [ht]; exact hR.tge)
  rcases regime s rfl with ⟨s0, h0, f0⟩
  rcases MemM1.Callees.tsi acc.ss acc va size s0 with ⟨ti, s1, h1, f1⟩
  have hs1 : s1.regs = s.regs := f1.1.trans f0.1
  have hm1 : s1.mem = s.mem := f1.2.1.trans f0.2.1
  let P : AddressDescriptor → State → Prop := fun ipa u =>
    ipa.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
      ipa.memattrs.memtype = .MemType_Normal ∧ ipa.fault.statuscode = .Fault_None ∧
      u.regs = MemM1.IF.clrGP s.regs ∧ u.mem = s.mem
  have hP : ∀ ad t u, P ad t → Frame t u → P ad u := fun _ _ _ ⟨a1, a2, a3, a4, a5⟩ fu =>
    ⟨a1, a2, a3, fu.1.trans a4, fu.2.1.trans a5⟩
  rcases MemM1.Full.full va acc aligned { s1 with events := s1.events.push (.translationStart ti) } P hP
      hA.ss (fun t ht => regime t (ht.1.trans hs1))
      (fun f t ht hf => by
        have htr : t.regs = s.regs := ht.1.trans hs1
        have htm : t.mem = s.mem := ht.2.1.trans hm1
        rcases MemM1.S1TIF.s1t_if f va hva B hB aligned acc t _ rfl hf hA.el hA.ifetch hA.ss hA.ls64
            hA.tx hA.nf hA.ff (by rw [htr]; exact hR.noPOE) (by rw [htr]; exact hR.noPAN)
            (MemM1.Bits.en acc.acctype t (by rw [htr]; exact hR.m))
            (fun t' ht' => by
              rcases hW t' (ht'.1.trans htr) (ht'.2.1.trans htm) with
                ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, hwk⟩
              exact ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, fun f' v hf' hv =>
                hwk f' v hf' (hv.1.trans htr) (hv.2.1.trans htm)⟩) with
          ⟨fr, ipa, u, h, hfr, hpa, hmt, hif, fur, fum⟩
        exact ⟨fr, ipa, u, h, hfr, hpa, hmt, hif, fur.trans (by rw [htr]), fum.trans htm⟩) with
    ⟨ad, t, hfull, hpa, hmt, hadf, htr, htm⟩
  rcases MemM1.Debug.no_fault va acc size t (by rw [htr]; exact hR.el0) (by rw [htr]; exact hR.noRME)
      (by rw [htr]; exact hR.aa64el0) (by rw [htr]; exact hR.ns)
      (by rw [htr]; exact MemM1.Bits.mde _ hR.mde) (by rw [htr]; exact MemM1.Bits.hde _ hR.hde) with
    ⟨df, t2, hdbg, hdf, f2⟩
  rcases translateIF va acc aligned size s .Regime_EL20 s0 ti s1 ad t df t2 hA.ifetch h0 h1 hfull hadf
      (MemM1.Callees.rme t (by rw [htr]; exact hR.noRME)) hdbg with ⟨t3, h3, hr3, hm3⟩
  exact ⟨_, t3, h3, hdf, hpa, hmt, hr3.trans (f2.1.trans htr), hm3.trans (f2.2.1.trans htm)⟩

#print axioms coreIF

/-- `coreIF` when `InGuardedPage` is already clear: registers and memory unchanged. -/
theorem coreIF_unchanged (va : BitVec 64) (hva : va.toNat < 2^48) (B : BitVec 56)
    (hB : B &&& 0xfff#56 = 0#56) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (hR : Witness.Regs20 s.regs) (hA : AccIF acc) (hW : WalkOKIF acc s va B)
    (hGP : s.regs.bank_Bool .InGuardedPage = false) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  rcases coreIF va hva B hB acc aligned size s hR hA hW with ⟨ad, t, h, a1, a2, a3, a4, a5⟩
  exact ⟨ad, t, h, a1, a2, a3, a4.trans (MemM1.IF.clrGP_self _ hGP), a5⟩

#print axioms coreIF_unchanged
end MemM1.WitnessIF
