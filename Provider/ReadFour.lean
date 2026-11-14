-- 4-byte actual Sail load. Adapted from NativeMte2.Read.single8 (76d66aa9)
-- and the signed 4-byte physical read/alignment proof.
import NativeMte2.Read
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

namespace ReleaseProfile.ReadFour
#check "CURRENT_DECL single4"
theorem single4 (a : BitVec 64) (aligned ispair : Bool) (halign : a.toNat % 4 = 0) (acc : AccessDescriptor) (s : NativeMte2.State)
    (pa : BitVec 56) (data : BitVec (4 * 8)) (hA : AccDR2 acc) (hTco : TcoAt s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → NativeMte2.State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a (clearTagCheck acc) aligned ((4 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      PostRegs t1.regs ∧
      (∀ i < 4, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ PostRegs t1.regs ∧ AArch64_MemSingle_read__1 a 4 acc aligned ispair s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 4 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind (clearTagCheck acc)) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1631 s with ⟨l1, s1, e1, f1⟩
  rcases bits_normal (Sail.Int.toNatChecked (((4 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have F2 := frame_trans f1 f2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  have hp := hTco.transport F2
  have eM2 : HaveMTE2Ext () s2 = .ok true s2 := (have_mte2 s2).trans (by rw [hp.mte2])
  obtain ⟨u,e4,fu⟩ := prepare_if_tco a acc s2 hp hel
  simp only [Bind.bind,EStateM.bind,Pure.pure,EStateM.pure] at e4
  rcases hTA u (frame_trans F2 fu) with ⟨ad, t1, e5, hf, hpa, hmt, hin, hout, hP, hm, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  have e7 := have_mte2 t2
  have hA' : AccDR2 (clearTagCheck acc) :=
    ⟨hA.gpr,hA.tx,hA.exclusive,hA.atomicop,hA.acqsc,hA.acqpc,hA.relsc⟩
  have hspe3 : Register.SPESampleInFlight.get t2.regs = false := by rw [f6.1]; exact hP.spe
  rcases occ_normal 1632 t2 with ⟨l2, t4, e8, f8⟩
  rcases S1EntryCalleesExtra.bool_normal l2 t4 with ⟨b2, t5, e9, f9⟩
  rcases occ_normal 1633 t5 with ⟨l3, t6, e10, f10⟩
  rcases physstat_normal l3 t6 with ⟨ps, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans f6 f8) f9) f10) f11
  have hm7 : ∀ i < 4, t7.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8) := by
    rw [G7.2.1, hpa]; exact hm
  have e12 := physRead ad (clearTagCheck acc) t7 data (by rw [hpa]; exact hio) hm7
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned_gen a 4 (by unfold SizeOK; omega) halign
  have hai := allIn_gen a 4 (by unfold SizeOK; omega) halign s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hwb : (MemType.MemType_Normal == MemType.MemType_Normal && MemAttr_WB == MemAttr_WB &&
      MemAttr_WB == MemAttr_WB) = true := by decide
  have hsz : ((4 : Nat) == 1 || (((4 : Nat) == 2 || (((4 : Nat) == 4 || (((4 : Nat) == 8 || (4 : Nat) == 16))))))) = true := by
    decide
  refine ⟨ad, t1, { t7 with events := t7.events.push (.memRead ad.paddress.address.toNat 4
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind (clearTagCheck acc)) false) }, hQ, hP, ?_, ?_, G7.1, G7.2.1⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_read__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e1, e2, e3, eM2, e4, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai,
      hA'.exclusive, hA'.atomicop, hA'.acqsc, hA'.acqpc, hA'.relsc, hA'.tx, clearTagCheck_tag, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, hmt, hin, hout, hwb,
      Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]

#check "CURRENT_DECL memRead4"
theorem memRead4 (a : BitVec 64) (halign : a.toNat % 4 = 0) (acc : AccessDescriptor) (s : NativeMte2.State)
    (pa : BitVec 56) (data : BitVec (4 * 8)) (hA : AccDR2 acc) (hTco : TcoAt s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → NativeMte2.State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a (clearTagCheck acc) true ((4 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs t1.regs ∧
      (∀ i < 4, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_read a 4 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 4 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((4 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  obtain ⟨lse, e5⟩ : ∃ b, HaveLSE2Ext () s3 = .ok b s3 := ⟨_, rfl⟩
  rcases single4 a true false halign acc s3 pa data hA (hTco.transport F3) hel Q
      (fun u fu => hTA u (frame_trans F3 fu)) hio with
    ⟨ad, t1, t, hQ, hP, e6, hte, htr, htm⟩
  have hPt : PostRegs t.regs := htr ▸ hP
  rcases MemM1.MemReadDBE.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hal := isAligned_gen a 4 (by unfold SizeOK; omega) halign
  have hai := allIn_gen a 4 (by unfold SizeOK; omega) halign s3
  have hsz2 : (((((4 : Nat) == 1 || (4 : Nat) == 2) || (4 : Nat) == 4) || (4 : Nat) == 8) || (4 : Nat) == 16) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  rw [clearTagCheck_kind] at hte
  refine ⟨ad, t1, t', hQ, ?_, f7.2.2.trans hte, f7.1.trans htr, f7.2.1.trans htm⟩
  cases lse <;>
  · unfold Mem_read Mem_read__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz2, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hga, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]

#print axioms single4
#print axioms memRead4
end ReleaseProfile.ReadFour
