-- Actual Mem_set wrappers over the MTE2-on Sail preparation, without TagOK.
import NativeMte2.Store
import MemM1.MemWriteD6

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD4
open MemM1.MemWriteD5 ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
open NativeMte2

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000
set_option linter.unusedSimpArgs false

namespace ReleaseProfile.NaturalStores
abbrev State := NativeMte2.State

theorem littleEndian (acc : AccessDescriptor) (s : State) (hA : AccDWT acc)
    (hP : MemM1.MemReadD.PostRegs s.regs) : LittleEndian acc s := by
  intro u fu
  rw [hA.base.gpr]
  exact MemM1.MemReadDBE.be_false u (by rw [fu.1]; exact hP.el0) (by rw [fu.1]; exact hP.nrw)
    (by rw [fu.1]; exact hP.noRME) (by rw [fu.1]; exact hP.vhe) (by rw [fu.1]; exact hP.aa64el0)
    (by rw [fu.1]; exact hP.ns) (by rw [fu.1]; exact hP.e2h) (by rw [fu.1]; exact hP.tge)
    (by rw [fu.1]; exact hP.e0e)

#check "CURRENT_DECL memSet"
theorem memSet (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (n * 8)) (hA : AccDWT acc)
    (hTco : TcoAt s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a (clearTagCheck acc) true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ t1.regs.bank_Bool .SPESampleInFlight = false ∧ Q ad t1)
    (hio : NotMMIO pa) (hLE : LittleEndian acc s) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_set a n acc v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat n (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) := by
  rcases occ_normal 1646 s with ⟨l1, s1, e1, f1⟩
  rcases constraint_normal l1 s1 with ⟨c, s2, e2, f2⟩
  rcases occ_normal 1647 s2 with ⟨l2, s3, e3, f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp, s4, e4, f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  rcases hLE s4 F4 with ⟨s5, e5, f5⟩
  have F5 := frame_trans F4 f5
  obtain ⟨lse, e6⟩ : ∃ b, HaveLSE2Ext () s5 = .ok b s5 := ⟨_, rfl⟩
  rcases NativeMte2.Store.store_natural a n hn true false ha acc s5 pa v hA (hTco.transport F5) hel Q
      (fun u fu => hTA u (frame_trans F5 fu)) hio with
    ⟨ad, t1, t, hQ, hset, hev, hreg, hmem⟩
  rw [clearTagCheck_kind] at hev
  refine ⟨ad, t1, t, hQ, ?_, hev, hreg, hmem⟩
  have hal := isAligned_gen a n hn ha
  have hai := allIn_gen a n hn ha s5
  have hsz := sizeOK_beq n hn
  have hsz2 : ((((n == 1) || (n == 2)) || (n == 4)) || (n == 8) || (n == 16)) = true := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  have hsimd : (BEq.beq acc.acctype AccessType.AccessType_ASIMD) = false := by
    rw [hA.base.gpr]; rfl
  cases lse <;>
  · unfold Mem_set Mem_set__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hsz2, e1, e2, e3, e4, e5, e6, hal, hai, hsimd, hset, Sail.BitVec.castWidth_eq,
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, Bool.and_true, Bool.true_and, ↓reduceIte, ite_self]
    done

#print axioms memSet

#check "CURRENT_DECL memSetPair"
theorem memSetPair (a : BitVec 64) (ha : a.toNat % 16 = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (16 * 8)) (hA : AccDWT acc)
    (hTco : TcoAt s) (hel : acc.el = EL0) (hLSE : s.regs.FeatureImpl[111] = true)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a (clearTagCheck acc) true ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ Q ad t1)
    (hio : NotMMIO pa) (hLE : LittleEndian acc s) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat 16 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * 16) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat 16
        (fun j => (Sail.BitVec.castWidth (m := 8 * 16) v).extractLsb' (8 * j) 8) := by
  rcases occ_normal 1646 s with ⟨l1, s1, e1, f1⟩
  rcases constraint_normal l1 s1 with ⟨c, s2, e2, f2⟩
  rcases occ_normal 1647 s2 with ⟨l2, s3, e3, f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp, s4, e4, f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  rcases hLE s4 F4 with ⟨s5, e5, f5⟩
  have F5 := frame_trans F4 f5
  have e6 := MemM1.MemWriteD5.lse2_on s5 (by rw [F5.1]; exact hLSE)
  have size16 : SizeOK 16 := by unfold SizeOK; omega
  rcases NativeMte2.Store.store_natural a 16 size16 true true ha acc s5 pa v hA (hTco.transport F5) hel Q
      (fun u fu => hTA u (frame_trans F5 fu)) hio with
    ⟨ad, t1, t, hQ, hset, hev, hreg, hmem⟩
  rw [clearTagCheck_kind] at hev
  refine ⟨ad, t1, t, hQ, ?_, hev, hreg, hmem⟩
  have hn8 : SizeOK 8 := by unfold SizeOK; omega
  have hn16 : SizeOK 16 := by unfold SizeOK; omega
  have hal8 := isAligned_gen a 8 hn8 (by omega)
  have hai := allIn_gen a 16 hn16 ha s5
  have h16 : ((((16 == 1) || (16 == 2)) || (16 == 4)) || (16 == 8) || (16 == 16)) = true := by decide
  have hhalf : Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2) = 8 := by decide
  have hsimd : (BEq.beq acc.acctype AccessType.AccessType_ASIMD) = false := by
    rw [hA.base.gpr]; rfl
  unfold Mem_set__1 Mem_set__2
  simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
    PreSail.assert, h16, e1, e2, e3, e4, e5, e6, hhalf, hal8, hai, hsimd, hset, Sail.BitVec.castWidth_eq,
    Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.and_true, Bool.true_and, Bool.or_true, Bool.true_or, ↓reduceIte, ite_self]
  done

#print axioms memSetPair
end ReleaseProfile.NaturalStores
