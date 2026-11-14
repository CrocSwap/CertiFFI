import DefaultPrefix
import ReadFour
import DefaultReadTrace1
import DefaultReadTraceFour
import DefaultReadTrace8

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open NativeMte2
open MemM1.MemWriteD1 MemM1.MemWriteD4 MemM1.MemWriteD5 MemM1.MemWriteD6

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000
set_option linter.unusedSimpArgs false

namespace ReleaseProfile.DefaultNaturalReads

#check "CURRENT_DECL memRead1_trace"
theorem memRead1_trace (a : BitVec 64) (acc : AccessDescriptor) (s : NativeMte2.State)
    (pa : BitVec 56) (data : BitVec (1 * 8)) (hA : AccDR2 acc) (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → NativeMte2.State → Prop)
    (hTA : ∀ (prepared : AccessDescriptor) u,
      prepared = { acc with tagchecked := prepared.tagchecked } →
      NativeMteTagCheck.StatusTrace.TraceFrame s u → ∃ ad t1,
      AArch64_TranslateAddress a prepared true ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs t1.regs ∧ NativeMteTagCheck.DefaultAt catalogue t1 ∧
      (∀ value after, HaveTME () t1 = .ok value after → NativeMteTagCheck.TagStatusOK after) ∧
      (∀ i < 1, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t draws, Q ad t1 ∧ Mem_read a 1 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 1 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem ∧
      NativeMteTagCheck.ChoiceDelta s t draws ∧ draws ≤ 1 := by
  have halign : a.toNat % 1 = 0 := Nat.mod_one _
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1640 s (by decide) with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1641 s1 (by decide) with ⟨l2, s2, e3, f2⟩
  rcases NativeMteTagCheck.StatusTrace.bits_trace (Sail.Int.toNatChecked (((1 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have traceF3 := NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans f1 f2) f3
  have F3 := NativeMteTagCheck.StatusTrace.to_frame traceF3
  obtain ⟨lse, e5⟩ : ∃ b, HaveLSE2Ext () s3 = .ok b s3 := ⟨_, rfl⟩
  rcases DefaultRead1.single1_trace a true false halign acc s3 pa data hA catalogue (controls.transport F3) hel Q
      (fun prepared u eq fu => hTA prepared u eq (NativeMteTagCheck.StatusTrace.frame_trans traceF3 fu)) hio with
    ⟨ad, t1, t, draws, hQ, hP, e6, hte, htr, htm, callDelta, drawBound⟩
  have hPt : PostRegs t.regs := htr ▸ hP
  rcases DefaultPrefix.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hal := MemM1.MemReadD.isAligned1 a halign
  have hai := MemM1.MemReadD.allIn1 a halign s3
  have hsz2 : (((((1 : Nat) == 1 || (1 : Nat) == 2) || (1 : Nat) == 4) || (1 : Nat) == 8) || (1 : Nat) == 16) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  have totalDelta : NativeMteTagCheck.ChoiceDelta s t' draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans traceF3.2.2.2 callDelta) f7.2.2.2
  refine ⟨ad, t1, t', draws, hQ, ?_, f7.2.2.1.trans hte, f7.1.trans htr,
    f7.2.1.trans htm, totalDelta, drawBound⟩
  cases lse <;>
  · unfold Mem_read Mem_read__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz2, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hga, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]

#print axioms memRead1_trace

#check "CURRENT_DECL memRead8_trace"
theorem memRead8_trace (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (s : NativeMte2.State)
    (pa : BitVec 56) (data : BitVec (8 * 8)) (hA : AccDR2 acc) (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → NativeMte2.State → Prop)
    (hTA : ∀ (prepared : AccessDescriptor) u,
      prepared = { acc with tagchecked := prepared.tagchecked } →
      NativeMteTagCheck.StatusTrace.TraceFrame s u → ∃ ad t1,
      AArch64_TranslateAddress a prepared true ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs t1.regs ∧ NativeMteTagCheck.DefaultAt catalogue t1 ∧
      (∀ value after, HaveTME () t1 = .ok value after → NativeMteTagCheck.TagStatusOK after) ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t draws, Q ad t1 ∧ Mem_read a 8 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 8 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem ∧
      NativeMteTagCheck.ChoiceDelta s t draws ∧ draws ≤ 1 := by
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1640 s (by decide) with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1641 s1 (by decide) with ⟨l2, s2, e3, f2⟩
  rcases NativeMteTagCheck.StatusTrace.bits_trace (Sail.Int.toNatChecked (((8 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have traceF3 := NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans f1 f2) f3
  have F3 := NativeMteTagCheck.StatusTrace.to_frame traceF3
  obtain ⟨lse, e5⟩ : ∃ b, HaveLSE2Ext () s3 = .ok b s3 := ⟨_, rfl⟩
  rcases DefaultRead8.single8_trace a true false halign acc s3 pa data hA catalogue (controls.transport F3) hel Q
      (fun prepared u eq fu => hTA prepared u eq (NativeMteTagCheck.StatusTrace.frame_trans traceF3 fu)) hio with
    ⟨ad, t1, t, draws, hQ, hP, e6, hte, htr, htm, callDelta, drawBound⟩
  have hPt : PostRegs t.regs := htr ▸ hP
  rcases DefaultPrefix.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hal := MemM1.MemReadD.isAligned8 a halign
  have hai := MemM1.MemReadD.allIn8 a halign s3
  have hsz2 : (((((8 : Nat) == 1 || (8 : Nat) == 2) || (8 : Nat) == 4) || (8 : Nat) == 8) || (8 : Nat) == 16) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  have totalDelta : NativeMteTagCheck.ChoiceDelta s t' draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans traceF3.2.2.2 callDelta) f7.2.2.2
  refine ⟨ad, t1, t', draws, hQ, ?_, f7.2.2.1.trans hte, f7.1.trans htr,
    f7.2.1.trans htm, totalDelta, drawBound⟩
  cases lse <;>
  · unfold Mem_read Mem_read__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz2, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hga, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]

#print axioms memRead8_trace
#check "CURRENT_DECL memRead4_trace"
theorem memRead4_trace (a : BitVec 64) (halign : a.toNat % 4 = 0) (acc : AccessDescriptor) (s : NativeMte2.State)
    (pa : BitVec 56) (data : BitVec (4 * 8)) (hA : AccDR2 acc) (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → NativeMte2.State → Prop)
    (hTA : ∀ (prepared : AccessDescriptor) u,
      prepared = { acc with tagchecked := prepared.tagchecked } →
      NativeMteTagCheck.StatusTrace.TraceFrame s u → ∃ ad t1,
      AArch64_TranslateAddress a prepared true ((4 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs t1.regs ∧ NativeMteTagCheck.DefaultAt catalogue t1 ∧
      (∀ value after, HaveTME () t1 = .ok value after → NativeMteTagCheck.TagStatusOK after) ∧
      (∀ i < 4, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t draws, Q ad t1 ∧ Mem_read a 4 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 4 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem ∧
      NativeMteTagCheck.ChoiceDelta s t draws ∧ draws ≤ 1 := by
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1640 s (by decide) with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases NativeMteTagCheck.StatusTrace.occ_trace 1641 s1 (by decide) with ⟨l2, s2, e3, f2⟩
  rcases NativeMteTagCheck.StatusTrace.bits_trace (Sail.Int.toNatChecked (((4 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have traceF3 := NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans f1 f2) f3
  have F3 := NativeMteTagCheck.StatusTrace.to_frame traceF3
  obtain ⟨lse, e5⟩ : ∃ b, HaveLSE2Ext () s3 = .ok b s3 := ⟨_, rfl⟩
  rcases DefaultReadFour.single4_trace a true false halign acc s3 pa data hA catalogue (controls.transport F3) hel Q
      (fun prepared u eq fu => hTA prepared u eq (NativeMteTagCheck.StatusTrace.frame_trans traceF3 fu)) hio with
    ⟨ad, t1, t, draws, hQ, hP, e6, hte, htr, htm, callDelta, drawBound⟩
  have hPt : PostRegs t.regs := htr ▸ hP
  rcases DefaultPrefix.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hal := isAligned_gen a 4 (by unfold SizeOK; omega) halign
  have hai := allIn_gen a 4 (by unfold SizeOK; omega) halign s3
  have hsz2 : (((((4 : Nat) == 1 || (4 : Nat) == 2) || (4 : Nat) == 4) || (4 : Nat) == 8) || (4 : Nat) == 16) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  have totalDelta : NativeMteTagCheck.ChoiceDelta s t' draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans traceF3.2.2.2 callDelta) f7.2.2.2
  refine ⟨ad, t1, t', draws, hQ, ?_, f7.2.2.1.trans hte, f7.1.trans htr,
    f7.2.1.trans htm, totalDelta, drawBound⟩
  cases lse <;>
  · unfold Mem_read Mem_read__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz2, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hga, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]


#print axioms memRead4_trace
end ReleaseProfile.DefaultNaturalReads
