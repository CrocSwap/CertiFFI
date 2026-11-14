import MemM1.M1CoreIF
import MemM1.S1TIFE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace MemM1.WitnessIFE
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.WitnessIF

/-- `WitnessIF.translateIF` with the final state exposed: TranslateAddress (IFETCH) returns
    `{ad with fault := df, vaddress := va}` and appends exactly the translation-end event. -/
theorem translateIFE (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
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
    AArch64_TranslateAddress va acc aligned size s =
        .ok { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }
          { t2 with events := t2.events.push (Event.translationEnd
            { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }) } := by
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
#print axioms translateIFE

/-- The fixed fields of the translation-start record (`vmid`, `asid`, `cnp` come from the
    TLB context and are not constrained here). -/
theorem tsi_fields (R : Regime) (ss : SecurityState) (acc : AccessDescriptor) (va : BitVec 64)
    (size : Int) (s t : State) (ti : TranslationStartInfo)
    (h : AArch64_GetTranslationStartInfo R ss acc va size s = .ok ti t) :
    ti.ss = ss ∧ ti.regime = R ∧ ti.va = va ∧ ti.accdesc = acc ∧ ti.size = size := by
  unfold AArch64_GetTranslationStartInfo at h
  rcases occ_normal 1477 s with ⟨l, s1, e1, -⟩
  obtain ⟨tg, s2, e2⟩ : ∃ tg s2, undefined_TGx l () s1 = .ok tg s2 := ⟨_, _, rfl⟩
  simp only [Bind.bind, EStateM.bind, e1, e2, Pure.pure, EStateM.pure] at h
  cases hc : AArch64_GetS1TLBContext R ss va tg s2 with
  | ok c u =>
    rw [hc] at h
    injection h with h1
    subst h1
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | error e u => rw [hc] at h; cases h
#print axioms tsi_fields

/-- `WitnessIF.WalkOKIF` plus: the walk appends exactly `W` to the event log. -/
def WalkOKIFE (acc : AccessDescriptor) (s : State) (va : BitVec 64) (B : BitVec 56)
    (W : Array Event) : Prop :=
  ∀ t : State, t.regs = s.regs → t.mem = s.mem → ∃ wp u,
    AArch64_GetS1TTWParams .Regime_EL20 acc.ss va t = .ok wp u ∧ Frame t u ∧
    wp.d128 = 0#1 ∧ wp.pie = 0#1 ∧ wp.ds = 0#1 ∧ wp.tgx = .TGx_4KB ∧ wp.txsz = 16#6 ∧
    wp.wxn = 0#1 ∧ wp.e0pd = 0#1 ∧
    ∀ (f' : FaultRecord) (v : State), f'.statuscode = .Fault_None → v.regs = s.regs → v.mem = s.mem →
      ∃ fw wa w d u',
      AArch64_S1Walk f' wp va .Regime_EL20 acc 64 v = .ok (fw, wa, w, d) u' ∧
      fw.statuscode = .Fault_None ∧ u'.regs = v.regs ∧ u'.mem = v.mem ∧ u'.events = v.events ++ W ∧
      d.getLsbD 10 = true ∧ d.getLsbD 51 = false ∧
      w.memattrs.memtype = .MemType_Normal ∧ w.level = 3 ∧ w.contiguous = 0#1 ∧
      w.baseaddress = {paspace := .PAS_NonSecure, address := B} ∧
      w.permissions.uxn = 0#1 ∧ w.permissions.uxn_table = 0#1 ∧ w.guardedpage = 0#1

theorem walkOKIFE_weak (acc : AccessDescriptor) (s : State) (va : BitVec 64) (B : BitVec 56)
    (W : Array Event) (h : WalkOKIFE acc s va B W) : WalkOKIF acc s va B := by
  intro t htr htm
  rcases h t htr htm with ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, hwk⟩
  refine ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, fun f' v hf' hvr hvm => ?_⟩
  rcases hwk f' v hf' hvr hvm with ⟨fw, wa, w, d, u', e, b1, b2, b3, _, rest⟩
  exact ⟨fw, wa, w, d, u', e, b1, b2, b3, rest⟩

theorem ev_shape (a W : Array Event) (x y : Event) :
    (a.push x ++ W).push y = a ++ (#[x] ++ W ++ #[y]) := by
  rw [Array.push_eq_append, Array.push_eq_append]
  simp only [Array.append_assoc]

/-- The translation-start record of an IFETCH TranslateAddress at `va` (size `size`): the value the
    actual `AArch64_GetTranslationStartInfo` returns on a state with the registers, memory and
    events of `s`; its fixed fields are pinned. -/
def TSIOK (ti : TranslationStartInfo) (acc : AccessDescriptor) (va : BitVec 64) (size : Int)
    (s : State) : Prop :=
  ti.ss = .SS_NonSecure ∧ ti.regime = .Regime_EL20 ∧ ti.va = va ∧ ti.accdesc = acc ∧ ti.size = size ∧
  ∃ u u', Frame s u ∧ AArch64_GetTranslationStartInfo .Regime_EL20 acc.ss acc va size u = .ok ti u'

/-- Event-exact core (IFETCH): as `WitnessIF.coreIF`, plus `ad.vaddress = va` and the exact event
    log: translation start, the walk's events `W`, translation end. -/
theorem coreIFE (va : BitVec 64) (hva : va.toNat < 2^48) (B : BitVec 56)
    (hB : B &&& 0xfff#56 = 0#56) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (W : Array Event)
    (hR : Witness.Regs20 s.regs) (hA : AccIF acc) (hW : WalkOKIFE acc s va B W) :
    ∃ ti ad t, AArch64_TranslateAddress va acc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.vaddress = va ∧
      t.regs = MemM1.IF.clrGP s.regs ∧ t.mem = s.mem ∧
      t.events = s.events ++ (#[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad]) ∧
      TSIOK ti acc va size s := by
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
  have he1 : s1.events = s.events := f1.2.2.trans f0.2.2
  let s1' : State := { s1 with events := s1.events.push (.translationStart ti) }
  let P : AddressDescriptor → State → Prop := fun ipa u =>
    ipa.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
      ipa.memattrs.memtype = .MemType_Normal ∧ ipa.fault.statuscode = .Fault_None ∧
      u.regs = MemM1.IF.clrGP s.regs ∧ u.mem = s.mem ∧ u.events = s1'.events ++ W
  have hP : ∀ ad t u, P ad t → Frame t u → P ad u := fun _ _ _ ⟨a1, a2, a3, a4, a5, a6⟩ fu =>
    ⟨a1, a2, a3, fu.1.trans a4, fu.2.1.trans a5, fu.2.2.trans a6⟩
  rcases MemM1.Full.full va acc aligned s1' P hP
      hA.ss (fun t ht => regime t (ht.1.trans hs1))
      (fun f t ht hf => by
        have htr : t.regs = s.regs := ht.1.trans hs1
        have htm : t.mem = s.mem := ht.2.1.trans hm1
        rcases MemM1.S1TIFE.s1t_ife W f va hva B hB aligned acc t _ rfl hf hA.el hA.ifetch hA.ss hA.ls64
            hA.tx hA.nf hA.ff (by rw [htr]; exact hR.noPOE) (by rw [htr]; exact hR.noPAN)
            (MemM1.Bits.en acc.acctype t (by rw [htr]; exact hR.m))
            (fun t' ht' => by
              rcases hW t' (ht'.1.trans htr) (ht'.2.1.trans htm) with
                ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, hwk⟩
              exact ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, fun f' v hf' hv =>
                hwk f' v hf' (hv.1.trans htr) (hv.2.1.trans htm)⟩) with
          ⟨fr, ipa, u, h, hfr, hpa, hmt, hif, fur, fum, fue⟩
        exact ⟨fr, ipa, u, h, hfr, hpa, hmt, hif, fur.trans (by rw [htr]), fum.trans htm,
          fue.trans (by rw [ht.2.2])⟩) with
    ⟨ad, t, hfull, hpa, hmt, hadf, htr, htm, hte⟩
  rcases MemM1.Debug.no_fault va acc size t (by rw [htr]; exact hR.el0) (by rw [htr]; exact hR.noRME)
      (by rw [htr]; exact hR.aa64el0) (by rw [htr]; exact hR.ns)
      (by rw [htr]; exact MemM1.Bits.mde _ hR.mde) (by rw [htr]; exact MemM1.Bits.hde _ hR.hde) with
    ⟨df, t2, hdbg, hdf, f2⟩
  have h3 := translateIFE va acc aligned size s .Regime_EL20 s0 ti s1 ad t df t2 hA.ifetch h0 h1 hfull hadf
      (MemM1.Callees.rme t (by rw [htr]; exact hR.noRME)) hdbg
  rcases tsi_fields _ _ _ _ _ _ _ _ h1 with ⟨q1, q2, q3, q4, q5⟩
  refine ⟨ti, _, _, h3, hdf, hpa, hmt, ?_, f2.1.trans htr, f2.2.1.trans htm, ?_,
    ⟨q1.trans hA.ss, q2, q3, q4, q5, s0, s1, f0, h1⟩⟩
  · show Sail.BitVec.zeroExtend va 64 = va
    simp [Sail.BitVec.zeroExtend]
  · show (t2.events.push _) = _
    rw [f2.2.2, hte]
    show ((s1.events.push _) ++ W).push _ = _
    rw [he1, ev_shape]

#print axioms coreIFE
end MemM1.WitnessIFE
