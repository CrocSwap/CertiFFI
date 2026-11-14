import MemM1.MemWriteD3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemWriteD5
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3

/-- AccDW without the `tagchecked` flag (crypto's STRB post-index has tagchecked = TRUE). -/
structure AccDWT (acc : AccessDescriptor) : Prop where
  base : MemM1.Witness.Acc0 acc
  exclusive : acc.exclusive = false
  atomicop : acc.atomicop = false
  acqsc : acc.acqsc = false
  acqpc : acc.acqpc = false
  relsc : acc.relsc = false

theorem AccDW.toT {acc : AccessDescriptor} (h : AccDW acc) : AccDWT acc :=
  ⟨h.base, h.exclusive, h.atomicop, h.acqsc, h.acqpc, h.relsc⟩

/-- MTE closure: the access is not tag-checked, or FEAT_MTE2 (FeatureImpl bit 134) is absent. -/
def TagOK (acc : AccessDescriptor) (r : Regs) : Prop :=
  acc.tagchecked = false ∨ r.FeatureImpl[134] = false

/-- FEAT_MTE2 is bit 134 of FeatureImpl. -/
theorem mte2_off (s : State) (h : s.regs.FeatureImpl[134] = false) :
    HaveMTE2Ext () s = .ok false s := by
  have h' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_MTE2)]! = false := h
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_MTE2)]! s = _
  rw [h']

/-- FEAT_LSE2 is bit 111 of FeatureImpl. -/
theorem lse2_on (s : State) (h : s.regs.FeatureImpl[111] = true) :
    HaveLSE2Ext () s = .ok true s := by
  have h' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_LSE2)]! = true := h
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_LSE2)]! s = _
  rw [h']

theorem lse2_off (s : State) (h : s.regs.FeatureImpl[111] = false) :
    HaveLSE2Ext () s = .ok false s := by
  have h' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_LSE2)]! = false := h
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_LSE2)]! s = _
  rw [h']

theorem mte2_and (s : State) (acc : AccessDescriptor) (h : TagOK acc s.regs) :
    ∃ b, HaveMTE2Ext () s = .ok b s ∧ (b && acc.tagchecked) = false := by
  rcases h with h | h
  · exact ⟨_, rfl, by rw [h]; exact Bool.and_false _⟩
  · exact ⟨false, mte2_off s h, rfl⟩

/-- `set_skel` with `tagchecked` free: the two MTE tests (before and after TranslateAddress) are
    closed by `TagOK` on `s` and on the post-translation registers. -/
theorem set_skelT (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (n * 8)) (hA : AccDWT acc)
    (hT : TagOK acc s.regs)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK acc t1.regs ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ AArch64_MemSingle_set__1 a n acc true false v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat n (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) := by
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s = .ok b s := ⟨_, rfl⟩
  rcases mte2_and s acc hT with ⟨m1, e4, hb1⟩
  rcases hTA s ⟨rfl, rfl, rfl⟩ with ⟨ad, t1, e5, hf, hpa, hspe, hT1, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  rcases mte2_and t2 acc (by unfold TagOK; rw [f6.1]; exact hT1) with ⟨m2, e7, hb2⟩
  have hspe3 : Register.SPESampleInFlight.get t2.regs = false := by rw [f6.1]; exact hspe
  rcases occ_normal 1636 t2 with ⟨l2, t4, e8, f8⟩
  rcases physstat_normal l2 t4 with ⟨ps, t5, e9, f9⟩
  rcases occ_normal 1637 t5 with ⟨l3, t6, e10, f10⟩
  rcases S1EntryCalleesExtra.bool_normal l3 t6 with ⟨b3, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans f6 f8) f9) f10) f11
  have e12 := physWrite ad n acc t7 (Sail.BitVec.castWidth (m := 8 * n) v) (by rw [hpa]; exact hio)
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned_gen a n hn ha
  have hai := allIn_gen a n hn ha s
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hsz := sizeOK_beq n hn
  refine ⟨ad, t1, { t7 with
      events := t7.events.push (.memWrite ad.paddress.address.toNat n (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) none)
      mem := wfold t7.mem ad.paddress.address.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) },
    hQ, ?_, ?_, G7.1, ?_⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa]
  · dsimp only
    rw [G7.2.1, hpa]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_set__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e3, e4, hb1, e5, e6, e7, hb2, e8, e9, e10, e11, e12, hal, hai,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.base.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false]
    done

/-- The 16-byte PAIR access (`ispair = true`, the LSE2 STP route) at a 16-aligned `a`, when the
    translated memory attributes are Normal inner+outer Write-Back: `atomic` is true and the
    access is ONE 16-byte PhysMemWrite. (If the attributes are not WB, MemSingle_set instead
    issues TWO 8-byte PhysMemWrites at `pa` and `pa + 8`: hence the WB facts in the premise.) -/
theorem set_skel_pair (a : BitVec 64) (ha : a.toNat % 16 = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (16 * 8)) (hA : AccDWT acc)
    (hT : TagOK acc s.regs)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK acc t1.regs ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ AArch64_MemSingle_set__1 a 16 acc true true v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat 16 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * 16) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat 16
        (fun j => (Sail.BitVec.castWidth (m := 8 * 16) v).extractLsb' (8 * j) 8) := by
  have hn : SizeOK 16 := by unfold SizeOK; omega
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s = .ok b s := ⟨_, rfl⟩
  rcases mte2_and s acc hT with ⟨m1, e4, hb1⟩
  rcases hTA s ⟨rfl, rfl, rfl⟩ with ⟨ad, t1, e5, hf, hpa, hmt, hin, hout, hspe, hT1, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  rcases mte2_and t2 acc (by unfold TagOK; rw [f6.1]; exact hT1) with ⟨m2, e7, hb2⟩
  have hspe3 : Register.SPESampleInFlight.get t2.regs = false := by rw [f6.1]; exact hspe
  rcases occ_normal 1636 t2 with ⟨l2, t4, e8, f8⟩
  rcases physstat_normal l2 t4 with ⟨ps, t5, e9, f9⟩
  rcases occ_normal 1637 t5 with ⟨l3, t6, e10, f10⟩
  rcases S1EntryCalleesExtra.bool_normal l3 t6 with ⟨b3, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans f6 f8) f9) f10) f11
  have e12 := physWrite ad 16 acc t7 (Sail.BitVec.castWidth (m := 8 * 16) v) (by rw [hpa]; exact hio)
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned_gen a 16 hn ha
  have hai := allIn_gen a 16 hn ha s
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hsz := sizeOK_beq 16 hn
  have hwb : ((BEq.beq ad.memattrs.memtype MemType.MemType_Normal && (ad.memattrs.inner.attrs == MemAttr_WB)) &&
      (ad.memattrs.outer.attrs == MemAttr_WB)) = true := by
    rw [hmt, hin, hout]; decide
  refine ⟨ad, t1, { t7 with
      events := t7.events.push (.memWrite ad.paddress.address.toNat 16 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * 16) v)) none)
      mem := wfold t7.mem ad.paddress.address.toNat 16
        (fun j => (Sail.BitVec.castWidth (m := 8 * 16) v).extractLsb' (8 * j) 8) },
    hQ, ?_, ?_, G7.1, ?_⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa]
  · dsimp only
    rw [G7.2.1, hpa]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_set__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e3, e4, hb1, e5, e6, e7, hb2, e8, e9, e10, e11, e12, hal, hai, hwb,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.base.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false]
    done

#print axioms mte2_off
#print axioms lse2_on
#print axioms lse2_off
#print axioms set_skelT
#print axioms set_skel_pair
end MemM1.MemWriteD5
