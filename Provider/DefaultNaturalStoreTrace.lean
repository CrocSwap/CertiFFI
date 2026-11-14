import DefaultNaturalStores
import DefaultStoreTrace
import DefaultPrefix
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

namespace ReleaseProfile.DefaultNaturalStores
#check "CURRENT_DECL memSet_trace"
theorem memSet_trace (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (n * 8)) (hA : AccDWT acc)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ (prepared : AccessDescriptor) u,
      prepared = { acc with tagchecked := prepared.tagchecked } →
      NativeMteTagCheck.StatusTrace.TraceFrame s u → ∃ ad t1,
      AArch64_TranslateAddress a prepared true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ t1.regs.bank_Bool .SPESampleInFlight = false ∧
      NativeMteTagCheck.DefaultAt catalogue t1 ∧
      (∀ value after, HaveTME () t1 = .ok value after → NativeMteTagCheck.TagStatusOK after) ∧ Q ad t1)
    (hio : NotMMIO pa) (hLE : LittleEndianTrace acc s) :
    ∃ ad t1 t draws, Q ad t1 ∧ Mem_set a n acc v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat n (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) ∧
      NativeMteTagCheck.ChoiceDelta s t draws ∧ draws ≤ 1 := by
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1646 s (by decide) with ⟨l1, s1, e1, f1⟩
  rcases DefaultPrefix.constraint_total l1 s1 with ⟨c, e2⟩
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1647 s1 (by decide) with ⟨l2, s3, e3, f3⟩
  rcases DefaultPrefix.bool_total l2 s3 with ⟨jp, e4⟩
  have traceF4 := NativeMteTagCheck.StatusTrace.frame_trans f1 f3
  rcases hLE s3 traceF4 with ⟨s5, e5, f5⟩
  have traceF5 := NativeMteTagCheck.StatusTrace.frame_trans traceF4 f5
  have F5 := NativeMteTagCheck.StatusTrace.to_frame traceF5
  obtain ⟨lse, e6⟩ : ∃ b, HaveLSE2Ext () s5 = .ok b s5 := ⟨_, rfl⟩
  rcases DefaultStores.store_natural_trace a n hn true false ha acc s5 pa v hA catalogue (controls.transport F5) hel Q
      (fun prepared u eq fu => hTA prepared u eq (NativeMteTagCheck.StatusTrace.frame_trans traceF5 fu)) hio with
    ⟨ad, t1, t, draws, hQ, hset, hev, hreg, hmem, callDelta, drawBound⟩
  have totalDelta : NativeMteTagCheck.ChoiceDelta s t draws := by
    simpa only [Nat.zero_add] using NativeMteTagCheck.choice_delta_trans traceF5.2.2.2 callDelta
  refine ⟨ad, t1, t, draws, hQ, ?_, hev, hreg, hmem, totalDelta, drawBound⟩
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

#print axioms memSet_trace

#check "CURRENT_DECL memSetPair_trace"
theorem memSetPair_trace (a : BitVec 64) (ha : a.toNat % 16 = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (16 * 8)) (hA : AccDWT acc)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s) (hel : acc.el = EL0) (hLSE : s.regs.FeatureImpl[111] = true)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ (prepared : AccessDescriptor) u,
      prepared = { acc with tagchecked := prepared.tagchecked } →
      NativeMteTagCheck.StatusTrace.TraceFrame s u → ∃ ad t1,
      AArch64_TranslateAddress a prepared true ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧
      NativeMteTagCheck.DefaultAt catalogue t1 ∧
      (∀ value after, HaveTME () t1 = .ok value after → NativeMteTagCheck.TagStatusOK after) ∧ Q ad t1)
    (hio : NotMMIO pa) (hLE : LittleEndianTrace acc s) :
    ∃ ad t1 t draws, Q ad t1 ∧ Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat 16 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * 16) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat 16
        (fun j => (Sail.BitVec.castWidth (m := 8 * 16) v).extractLsb' (8 * j) 8) ∧
      NativeMteTagCheck.ChoiceDelta s t draws ∧ draws ≤ 1 := by
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1646 s (by decide) with ⟨l1, s1, e1, f1⟩
  rcases DefaultPrefix.constraint_total l1 s1 with ⟨c, e2⟩
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1647 s1 (by decide) with ⟨l2, s3, e3, f3⟩
  rcases DefaultPrefix.bool_total l2 s3 with ⟨jp, e4⟩
  have traceF4 := NativeMteTagCheck.StatusTrace.frame_trans f1 f3
  rcases hLE s3 traceF4 with ⟨s5, e5, f5⟩
  have traceF5 := NativeMteTagCheck.StatusTrace.frame_trans traceF4 f5
  have F5 := NativeMteTagCheck.StatusTrace.to_frame traceF5
  have e6 := MemM1.MemWriteD5.lse2_on s5 (by rw [F5.1]; exact hLSE)
  have size16 : SizeOK 16 := by unfold SizeOK; omega
  rcases DefaultStores.store_natural_trace a 16 size16 true true ha acc s5 pa v hA catalogue (controls.transport F5) hel Q
      (fun prepared u eq fu => hTA prepared u eq (NativeMteTagCheck.StatusTrace.frame_trans traceF5 fu)) hio with
    ⟨ad, t1, t, draws, hQ, hset, hev, hreg, hmem, callDelta, drawBound⟩
  have totalDelta : NativeMteTagCheck.ChoiceDelta s t draws := by
    simpa only [Nat.zero_add] using NativeMteTagCheck.choice_delta_trans traceF5.2.2.2 callDelta
  refine ⟨ad, t1, t, draws, hQ, ?_, hev, hreg, hmem, totalDelta, drawBound⟩
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

#print axioms memSetPair_trace
end ReleaseProfile.DefaultNaturalStores
