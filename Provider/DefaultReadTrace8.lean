import NativeMte2.Read
import DefaultPrefix
import TagCheckFrames.Translation
import NativeMteTagCheck.Prepare
import NativeMteTagCheck.Transport
import MemM1.MemWriteD6

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD4 MemM1.MemWriteD5 MemM1.MemWriteD6
open NativeMte2

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000
set_option linter.unusedSimpArgs false

namespace ReleaseProfile.DefaultRead8
#check "CURRENT_DECL single8_trace"
theorem single8_trace (a : BitVec 64) (aligned ispair : Bool) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (s : NativeMte2.State)
    (pa : BitVec 56) (data : BitVec (8 * 8)) (hA : AccDR2 acc) (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → NativeMte2.State → Prop)
    (hTA : ∀ (prepared : AccessDescriptor) u, prepared = { acc with tagchecked := prepared.tagchecked } →
      NativeMteTagCheck.StatusTrace.TraceFrame s u → ∃ ad t1,
      AArch64_TranslateAddress a prepared aligned ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      PostRegs t1.regs ∧ NativeMteTagCheck.DefaultAt catalogue t1 ∧
      (∀ value after, HaveTME () t1 = .ok value after → NativeMteTagCheck.TagStatusOK after) ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t draws, Q ad t1 ∧ PostRegs t1.regs ∧ AArch64_MemSingle_read__1 a 8 acc aligned ispair s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 8 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem ∧
      NativeMteTagCheck.ChoiceDelta s t draws ∧ draws ≤ 1 := by
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1631 s (by decide) with ⟨l1, s1, e1, f1⟩
  rcases NativeMteTagCheck.StatusTrace.bits_trace (Sail.Int.toNatChecked (((8 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have traceF2 := NativeMteTagCheck.StatusTrace.frame_trans f1 f2
  have F2 := NativeMteTagCheck.StatusTrace.to_frame traceF2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  have hp := controls.transport F2
  obtain ⟨m2, eM2⟩ : ∃ b, HaveMTE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  obtain ⟨prepared, u, e4, preparedEq, fu, _⟩ := NativeMteTagCheck.StatusTrace.prepare_default catalogue a acc s2 hp hel
  have preparedEl : prepared.el = EL0 := by rw [preparedEq]; exact hel
  have e4if := e4
  simp only [NativeMte2.prepare, eM2,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at e4if
  rcases hTA prepared u preparedEq (NativeMteTagCheck.StatusTrace.frame_trans traceF2 fu) with
    ⟨ad, t1, e5, hf, hpa, hmt, hin, hout, hP, hDefault, hStatus, hm, hQ⟩
  have walkDelta := TagCheckFrames.translation_preserves a prepared aligned _ u ad t1 e5
  have prefixDelta : NativeMteTagCheck.ChoiceDelta s t1 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.StatusTrace.frame_trans traceF2 fu).2.2.2 walkDelta
  obtain ⟨tme, e6⟩ := ReleaseProfile.DefaultPrefix.tme_total t1
  have default2 := hDefault
  obtain ⟨t3, draws, eTag, fTag, _, tagDelta, drawBound⟩ := NativeMteTagCheck.StatusTrace.tagcheck_transport catalogue a ad prepared t1 default2
    preparedEl (fun _ _ => hStatus tme t1 e6)
  have eTagIf := eTag
  obtain ⟨m7, e7⟩ : ∃ b, HaveMTE2Ext () t1 = .ok b t1 := ⟨_, rfl⟩
  simp only [NativeMteTagCheck.checkedAccess, e7,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at eTagIf
  have hA' : AccDR2 prepared := by
    rw [preparedEq]
    exact ⟨hA.gpr,hA.tx,hA.exclusive,hA.atomicop,hA.acqsc,hA.acqpc,hA.relsc⟩
  have hspe3 : Register.SPESampleInFlight.get t3.regs = false := by rw [fTag.1]; exact hP.spe
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1632 t3 (by decide) with ⟨l2, t4, e8, f8⟩
  obtain ⟨b2, e9⟩ := ReleaseProfile.DefaultPrefix.bool_total l2 t4
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1633 t4 (by decide) with ⟨l3, t6, e10, f10⟩
  obtain ⟨ps, e11⟩ := NativeMteTagCheck.phys_status_total l3 t6
  have afterTrace := NativeMteTagCheck.StatusTrace.frame_trans f8 f10
  have G7 := frame_trans fTag (NativeMteTagCheck.StatusTrace.to_frame afterTrace)
  have totalDelta : NativeMteTagCheck.ChoiceDelta s t6 draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans prefixDelta tagDelta) afterTrace.2.2.2
  have hm7 : ∀ i < 8, t6.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8) := by
    rw [G7.2.1, hpa]; exact hm
  have e12 := physRead8 ad prepared t6 data (by rw [hpa]; exact hio) hm7
  have preparedKind : AccessDescriptor_to_Access_kind prepared = AccessDescriptor_to_Access_kind acc := by
    rw [preparedEq]
    rfl
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned_gen a 8 (by unfold SizeOK; omega) halign
  have hai := allIn_gen a 8 (by unfold SizeOK; omega) halign s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hwb : (MemType.MemType_Normal == MemType.MemType_Normal && MemAttr_WB == MemAttr_WB &&
      MemAttr_WB == MemAttr_WB) = true := by decide
  have hsz : ((8 : Nat) == 1 || (((8 : Nat) == 2 || (((8 : Nat) == 4 || (((8 : Nat) == 8 || (8 : Nat) == 16))))))) = true := by
    decide
  refine ⟨ad, t1, { t6 with events := t6.events.push (.memRead ad.paddress.address.toNat 8
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind prepared) false) }, draws, hQ, hP, ?_, ?_, G7.1, G7.2.1, totalDelta, drawBound⟩
  rotate_left
  · show (t6.events.push _) = _
    rw [G7.2.2, hpa, preparedKind]
  cases tag : prepared.tagchecked
  all_goals simp only [tag, Bool.and_false, Bool.and_true, Bool.false_eq_true, ite_true, ite_false, Pure.pure, EStateM.pure, Bind.bind, EStateM.bind] at eTagIf
  case false =>
    cases eTagIf
    cases lse <;> cases tme <;>
    · unfold AArch64_MemSingle_read__1
      simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
        PreSail.assert, tag, hsz, hnn, e1, e2, e3, eM2, e4if, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai,
        hA'.exclusive, hA'.atomicop, hA'.acqsc, hA'.acqpc, hA'.relsc, hA'.tx, IsFault, hfn, IsFault__2,
        CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, hmt, hin, hout, hwb,
        Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
        ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]

  case true =>
    cases m7
    case false =>
      simp only [Bool.false_eq_true, ite_false, Pure.pure, EStateM.pure] at eTagIf
      cases eTagIf
      cases lse <;> cases tme <;>
      · unfold AArch64_MemSingle_read__1
        simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
          PreSail.assert, tag, hsz, hnn, e1, e2, e3, eM2, e4if, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai,
          hA'.exclusive, hA'.atomicop, hA'.acqsc, hA'.acqpc, hA'.relsc, hA'.tx, IsFault, hfn, IsFault__2,
          CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, hmt, hin, hout, hwb,
          Bool.and_false, Bool.false_and, Bool.true_and,
          Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
          ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]
    case true =>
      have eTagT := eTag
      simp only [NativeMteTagCheck.checkedAccess, e7, Bool.true_and,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at eTagT
      simp only [tag, Bool.false_eq_true, ite_true, ite_false, Pure.pure, EStateM.pure, Bind.bind, EStateM.bind] at eTagT
      cases lse <;> cases tme <;>
      · unfold AArch64_MemSingle_read__1
        simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
          PreSail.assert, tag, hsz, hnn, e1, e2, e3, eM2, e4if, e5, e6, e7, eTagT, e8, e9, e10, e11, e12, hal, hai,
          hA'.exclusive, hA'.atomicop, hA'.acqsc, hA'.acqpc, hA'.relsc, hA'.tx, IsFault, hfn, IsFault__2,
          CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, hmt, hin, hout, hwb,
          Bool.and_false, Bool.false_and, Bool.true_and,
          Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
          ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]

#print axioms single8_trace
end ReleaseProfile.DefaultRead8
