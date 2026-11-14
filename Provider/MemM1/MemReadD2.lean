import MemM1.MemReadD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemReadD2
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD

/-! Crypto's exact read calls: LDRB post-index `Mem_read a 1` with tagchecked = TRUE (closed by
FEAT_MTE2 absent, FeatureImpl[134] = false), and LDP 64-bit `Mem_read__1 a 16 acc true` (LSE2) or
two `Mem_read _ 8` (no LSE2), under the strong translation premise. -/

/-- FEAT_MTE2 is bit 134 of FeatureImpl. -/
theorem mte2_off (s : State) (h : s.regs.FeatureImpl[134] = false) : HaveMTE2Ext () s = .ok false s := by
  have h' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_MTE2)]! = false := h
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_MTE2)]! s = _
  rw [h']

/-- FEAT_LSE2 is bit 111 of FeatureImpl. -/
theorem lse2_on (s : State) (h : s.regs.FeatureImpl[111] = true) : HaveLSE2Ext () s = .ok true s := by
  have h' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_LSE2)]! = true := h
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_LSE2)]! s = _
  rw [h']

/-- GPR data access, tagchecked unconstrained (LDRB post-index has tagchecked = true). -/
structure AccDR2 (acc : AccessDescriptor) : Prop where
  gpr : acc.acctype = .AccessType_GPR
  tx : acc.transactional = false
  exclusive : acc.exclusive = false
  atomicop : acc.atomicop = false
  acqsc : acc.acqsc = false
  acqpc : acc.acqpc = false
  relsc : acc.relsc = false

theorem kind_eq2 (acc : AccessDescriptor) (hA : AccDR2 acc) :
    AccessDescriptor_to_Access_kind acc =
      .AK_explicit { variety := .AV_plain, strength := .AS_normal } := by
  unfold AccessDescriptor_to_Access_kind
  rw [hA.gpr]
  simp only [hA.exclusive, hA.atomicop, hA.acqpc, hA.acqsc, hA.relsc, Bool.false_eq_true, ↓reduceIte,
    Bool.or_false]

theorem AccDR.toR2 {acc : AccessDescriptor} (h : AccDR acc) : AccDR2 acc :=
  ⟨h.gpr, h.tx, h.exclusive, h.atomicop, h.acqsc, h.acqpc, h.relsc⟩

/-- `PostRegs` plus FEAT_MTE2 absent (the one bit that closes the MTE tag-check path). -/
structure PostRegs2 (r : Regs) : Prop where
  post : PostRegs r
  noMTE2 : r.FeatureImpl[134] = false

theorem isAligned16 (a : BitVec 64) (h : a.toNat % 16 = 0) : IsAligned__1 a ((16 : Nat) : Int) = true := by
  have hx := MemM1.MemReadD.align_lit a 16 (by decide)
  unfold IsAligned__1
  rw [hx]
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp
  all_goals omega

theorem allIn16 (a : BitVec 64) (h : a.toNat % 16 = 0) (s : State) :
    AllInAlignedQuantity a ((16 : Nat) : Int) 16 s = .ok true s := by
  have hx : Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) (16 : Int) =
      BitVec.ofNat 64 ((BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1).toNat / 16 * 16) :=
    MemM1.MemReadD.align_lit _ 16 (by decide)
  have hx' : Align_bits a (16 : Int) = BitVec.ofNat 64 (a.toNat / 16 * 16) := MemM1.MemReadD.align_lit a 16 (by decide)
  unfold AllInAlignedQuantity
  simp only [ArmFull.assert, PreSail.assert, hx, hx', Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have hlt := a.isLt
  have e : (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1).toNat = a.toNat + 15 := by
    simp [BitVec.subInt, BitVec.addInt, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  rw [e]
  have e2 : (a.toNat + 15) / 16 * 16 = a.toNat / 16 * 16 := by omega
  rw [e2]
  simp
  rfl

theorem join128 (d : BitVec 128) :
    BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append (BitVec.append ((d.extractLsb' 120 8)) (d.extractLsb' 112 8)) (d.extractLsb' 104 8)) (d.extractLsb' 96 8)) (d.extractLsb' 88 8)) (d.extractLsb' 80 8)) (d.extractLsb' 72 8)) (d.extractLsb' 64 8)) (d.extractLsb' 56 8)) (d.extractLsb' 48 8)) (d.extractLsb' 40 8)) (d.extractLsb' 32 8)) (d.extractLsb' 24 8)) (d.extractLsb' 16 8)) (d.extractLsb' 8 8)) (d.extractLsb' 0 8) = d := by
  simp only [BitVec.append_eq]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 8) (by decide : 120 = 112 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 16) (by decide : 112 = 104 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 24) (by decide : 104 = 96 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 32) (by decide : 96 = 88 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 40) (by decide : 88 = 80 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 48) (by decide : 80 = 72 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 56) (by decide : 72 = 64 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 64) (by decide : 64 = 56 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 72) (by decide : 56 = 48 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 80) (by decide : 48 = 40 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 88) (by decide : 40 = 32 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 96) (by decide : 32 = 24 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 104) (by decide : 24 = 16 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 112) (by decide : 16 = 8 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 120) (by decide : 8 = 0 + 8)]
  exact BitVec.extractLsb'_eq_self

theorem join128' (d : BitVec 128) :
    (d.extractLsb' 120 8) +++ (d.extractLsb' 112 8) +++ (d.extractLsb' 104 8) +++ (d.extractLsb' 96 8) +++ (d.extractLsb' 88 8) +++ (d.extractLsb' 80 8) +++ (d.extractLsb' 72 8) +++ (d.extractLsb' 64 8) +++ (d.extractLsb' 56 8) +++ (d.extractLsb' 48 8) +++ (d.extractLsb' 40 8) +++ (d.extractLsb' 32 8) +++ (d.extractLsb' 24 8) +++ (d.extractLsb' 16 8) +++ (d.extractLsb' 8 8) +++ (d.extractLsb' 0 8) = d := by
  simpa only [BitVec.append_eq] using join128 d

theorem read16 (address : Nat) (data : BitVec 128) (s : State)
    (h : ∀ i < 16, s.mem[address + i]? = some (data.extractLsb' (8 * i) 8)) :
    (PreSail.readBytes 16 address : SailM (BitVec (8 * 16) × Option Bool)) s = .ok (data, none) s := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h6 := h 6 (by decide)
  have h7 := h 7 (by decide)
  have h8 := h 8 (by decide)
  have h9 := h 9 (by decide)
  have h10 := h 10 (by decide)
  have h11 := h 11 (by decide)
  have h12 := h 12 (by decide)
  have h13 := h 13 (by decide)
  have h14 := h 14 (by decide)
  have h15 := h 15 (by decide)
  simp only [Nat.add_zero, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [PreSail.readBytes, PreSail.readByte, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, Nat.add_assoc, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, join128']

theorem physRead16' (ad : AddressDescriptor) (acc : AccessDescriptor) (u : State) (data : BitVec (16 * 8))
    (hio : NotMMIO ad.paddress.address)
    (hmem : ∀ i < 16, u.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    PhysMemRead ad 16 acc none u =
      .ok (CreatePhysMemRetStatus .Fault_None, data)
        { u with events := u.events.push (.memRead ad.paddress.address.toNat 16
            (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind acc) false) } := by
  have g : (Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb ad.paddress.address
      (Sail.Int.toNatChecked ((Sail.BitVec.length ad.paddress.address : Int) -i 1)) 16) ==
      Sail.BitVec.castWidth (m := 40) (ZeroExtend1 (m := Sail.Int.toNatChecked (((56 -i 1) -i 16) +i 1))
        GIC_BASE)) = false := by
    simp only [Sail.BitVec.castWidth_eq, beq_eq_false_iff_ne]
    exact hio.1
  have ua : (Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb ad.paddress.address
      (Sail.Int.toNatChecked ((Sail.BitVec.length ad.paddress.address : Int) -i 1)) 16) ==
      Sail.BitVec.castWidth (m := 40) (ZeroExtend1 (m := Sail.Int.toNatChecked (((56 -i 1) -i 16) +i 1))
        UART_BASE)) = false := by
    simp only [Sail.BitVec.castWidth_eq, beq_eq_false_iff_ne]
    exact hio.2
  unfold PhysMemRead
  simp only [g, ua, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, ArmFull.ConcurrencyInterfaceV1.sail_mem_read, PreSail.sail_mem_read,
    PreSail.logEvent, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, read_request]
  have hr := read16 ad.paddress.address.toNat data { u with events := (u.events.push (Event.memRead ad.paddress.address.toNat 16 (Option.map (fun x => x.toNat) (some ad.vaddress)) (AccessDescriptor_to_Access_kind acc) false)) } hmem
  simp only [hr]
  rfl

/-- `AArch64_MemSingle_read__1 a 1 acc true false` with tagchecked unconstrained (FEAT_MTE2 absent)
    and the memory inner/outer write-back (so a pair access is single-copy atomic: one read). -/
theorem single2_1 (a : BitVec 64) (halign : a.toNat % 1 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (1 * 8)) (hA : AccDR2 acc) (hM2 : s.regs.FeatureImpl[134] = false)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      PostRegs2 t1.regs ∧
      (∀ i < 1, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ PostRegs2 t1.regs ∧ AArch64_MemSingle_read__1 a 1 acc true false s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 1 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1631 s with ⟨l1, s1, e1, f1⟩
  rcases bits_normal (Sail.Int.toNatChecked (((1 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have F2 := frame_trans f1 f2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  have e4 := mte2_off s2 (by rw [F2.1]; exact hM2)
  rcases hTA s2 F2 with ⟨ad, t1, e5, hf, hpa, hmt, hin, hout, hP, hm, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  have e7 := mte2_off t2 (by rw [f6.1]; exact hP.noMTE2)
  have hspe3 : Register.SPESampleInFlight.get t2.regs = false := by rw [f6.1]; exact hP.post.spe
  rcases occ_normal 1632 t2 with ⟨l2, t4, e8, f8⟩
  rcases S1EntryCalleesExtra.bool_normal l2 t4 with ⟨b2, t5, e9, f9⟩
  rcases occ_normal 1633 t5 with ⟨l3, t6, e10, f10⟩
  rcases physstat_normal l3 t6 with ⟨ps, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans f6 f8) f9) f10) f11
  have hm7 : ∀ i < 1, t7.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8) := by
    rw [G7.2.1, hpa]; exact hm
  have e12 := physRead1 ad acc t7 data (by rw [hpa]; exact hio) hm7
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := MemM1.MemReadD.isAligned1 a halign
  have hai := MemM1.MemReadD.allIn1 a halign s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hwb : (MemType.MemType_Normal == MemType.MemType_Normal && MemAttr_WB == MemAttr_WB &&
      MemAttr_WB == MemAttr_WB) = true := by decide
  have hsz : ((1 : Nat) == 1 || (((1 : Nat) == 2 || (((1 : Nat) == 4 || (((1 : Nat) == 8 || (1 : Nat) == 16))))))) = true := by
    decide
  refine ⟨ad, t1, { t7 with events := t7.events.push (.memRead ad.paddress.address.toNat 1
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind acc) false) }, hQ, hP, ?_, ?_, G7.1, G7.2.1⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_read__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, hmt, hin, hout, hwb,
      Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]

/-- `AArch64_MemSingle_read__1 a 8 acc true false` with tagchecked unconstrained (FEAT_MTE2 absent)
    and the memory inner/outer write-back (so a pair access is single-copy atomic: one read). -/
theorem single2_8 (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (8 * 8)) (hA : AccDR2 acc) (hM2 : s.regs.FeatureImpl[134] = false)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ PostRegs2 t1.regs ∧ AArch64_MemSingle_read__1 a 8 acc true false s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 8 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1631 s with ⟨l1, s1, e1, f1⟩
  rcases bits_normal (Sail.Int.toNatChecked (((8 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have F2 := frame_trans f1 f2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  have e4 := mte2_off s2 (by rw [F2.1]; exact hM2)
  rcases hTA s2 F2 with ⟨ad, t1, e5, hf, hpa, hmt, hin, hout, hP, hm, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  have e7 := mte2_off t2 (by rw [f6.1]; exact hP.noMTE2)
  have hspe3 : Register.SPESampleInFlight.get t2.regs = false := by rw [f6.1]; exact hP.post.spe
  rcases occ_normal 1632 t2 with ⟨l2, t4, e8, f8⟩
  rcases S1EntryCalleesExtra.bool_normal l2 t4 with ⟨b2, t5, e9, f9⟩
  rcases occ_normal 1633 t5 with ⟨l3, t6, e10, f10⟩
  rcases physstat_normal l3 t6 with ⟨ps, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans f6 f8) f9) f10) f11
  have hm7 : ∀ i < 8, t7.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8) := by
    rw [G7.2.1, hpa]; exact hm
  have e12 := physRead8 ad acc t7 data (by rw [hpa]; exact hio) hm7
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := MemM1.MemReadD.isAligned8 a halign
  have hai := MemM1.MemReadD.allIn8 a halign s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hwb : (MemType.MemType_Normal == MemType.MemType_Normal && MemAttr_WB == MemAttr_WB &&
      MemAttr_WB == MemAttr_WB) = true := by decide
  have hsz : ((8 : Nat) == 1 || (((8 : Nat) == 2 || (((8 : Nat) == 4 || (((8 : Nat) == 8 || (8 : Nat) == 16))))))) = true := by
    decide
  refine ⟨ad, t1, { t7 with events := t7.events.push (.memRead ad.paddress.address.toNat 8
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind acc) false) }, hQ, hP, ?_, ?_, G7.1, G7.2.1⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_read__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, hmt, hin, hout, hwb,
      Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]

/-- `AArch64_MemSingle_read__1 a 16 acc true true` with tagchecked unconstrained (FEAT_MTE2 absent)
    and the memory inner/outer write-back (so a pair access is single-copy atomic: one read). -/
theorem single2_16 (a : BitVec 64) (halign : a.toNat % 16 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (16 * 8)) (hA : AccDR2 acc) (hM2 : s.regs.FeatureImpl[134] = false)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ PostRegs2 t1.regs ∧ AArch64_MemSingle_read__1 a 16 acc true true s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 16 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1631 s with ⟨l1, s1, e1, f1⟩
  rcases bits_normal (Sail.Int.toNatChecked (((16 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have F2 := frame_trans f1 f2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  have e4 := mte2_off s2 (by rw [F2.1]; exact hM2)
  rcases hTA s2 F2 with ⟨ad, t1, e5, hf, hpa, hmt, hin, hout, hP, hm, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  have e7 := mte2_off t2 (by rw [f6.1]; exact hP.noMTE2)
  have hspe3 : Register.SPESampleInFlight.get t2.regs = false := by rw [f6.1]; exact hP.post.spe
  rcases occ_normal 1632 t2 with ⟨l2, t4, e8, f8⟩
  rcases S1EntryCalleesExtra.bool_normal l2 t4 with ⟨b2, t5, e9, f9⟩
  rcases occ_normal 1633 t5 with ⟨l3, t6, e10, f10⟩
  rcases physstat_normal l3 t6 with ⟨ps, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans f6 f8) f9) f10) f11
  have hm7 : ∀ i < 16, t7.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8) := by
    rw [G7.2.1, hpa]; exact hm
  have e12 := physRead16' ad acc t7 data (by rw [hpa]; exact hio) hm7
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned16 a halign
  have hai := allIn16 a halign s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hwb : (MemType.MemType_Normal == MemType.MemType_Normal && MemAttr_WB == MemAttr_WB &&
      MemAttr_WB == MemAttr_WB) = true := by decide
  have hsz : ((16 : Nat) == 1 || (((16 : Nat) == 2 || (((16 : Nat) == 4 || (((16 : Nat) == 8 || (16 : Nat) == 16))))))) = true := by
    decide
  refine ⟨ad, t1, { t7 with events := t7.events.push (.memRead ad.paddress.address.toNat 16
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind acc) false) }, hQ, hP, ?_, ?_, G7.1, G7.2.1⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_read__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, hmt, hin, hout, hwb,
      Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]

/-- `Mem_read a 1 acc` (LDRB) with tagchecked unconstrained: draws, the single access, BigEndian. -/
theorem memRead2_1 (a : BitVec 64) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (1 * 8)) (hA : AccDR2 acc) (hM2 : s.regs.FeatureImpl[134] = false)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 1, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_read a 1 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 1 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  have halign : a.toNat % 1 = 0 := Nat.mod_one _
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((1 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  obtain ⟨lse, e5⟩ : ∃ b, HaveLSE2Ext () s3 = .ok b s3 := ⟨_, rfl⟩
  rcases single2_1 a halign acc s3 pa data hA (by rw [F3.1]; exact hM2) Q
      (fun u fu => hTA u (frame_trans F3 fu)) hio with
    ⟨ad, t1, t, hQ, hP, e6, hte, htr, htm⟩
  have hPt : PostRegs t.regs := htr ▸ hP.post
  rcases MemM1.MemReadDBE.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hal := MemM1.MemReadD.isAligned1 a halign
  have hai := MemM1.MemReadD.allIn1 a halign s3
  have hsz2 : (((((1 : Nat) == 1 || (1 : Nat) == 2) || (1 : Nat) == 4) || (1 : Nat) == 8) || (1 : Nat) == 16) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  refine ⟨ad, t1, t', hQ, ?_, f7.2.2.trans hte, f7.1.trans htr, f7.2.1.trans htm⟩
  cases lse <;>
  · unfold Mem_read Mem_read__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz2, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hga, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]

/-- `Mem_read__1 a 16 acc true` (LDP 64-bit pair, FEAT_LSE2, a 16-aligned): one 16-byte access. -/
theorem memReadPair (a : BitVec 64) (halign : a.toNat % 16 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (16 * 8)) (hA : AccDR2 acc) (hM2 : s.regs.FeatureImpl[134] = false)
    (hLSE2 : s.regs.FeatureImpl[111] = true)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_read__1 a 16 acc true s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 16 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((16 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  have e5 := lse2_on s3 (by rw [F3.1]; exact hLSE2)
  rcases single2_16 a halign acc s3 pa data hA (by rw [F3.1]; exact hM2) Q
      (fun u fu => hTA u (frame_trans F3 fu)) hio with
    ⟨ad, t1, t, hQ, hP, e6, hte, htr, htm⟩
  have hPt : PostRegs t.regs := htr ▸ hP.post
  rcases MemM1.MemReadDBE.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hhalf : Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) = 8 := by decide
  have hal := MemM1.MemReadD.isAligned8 a (by omega)
  have hai := allIn16 a halign s3
  have hsz2 : (((((16 : Nat) == 1 || (16 : Nat) == 2) || (16 : Nat) == 4) || (16 : Nat) == 8) || (16 : Nat) == 16) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  refine ⟨ad, t1, t', hQ, ?_, f7.2.2.trans hte, f7.1.trans htr, f7.2.1.trans htm⟩
  unfold Mem_read__1 Mem_read__2
  simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
    PreSail.assert, hsz2, hhalf, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hga, Bool.and_false,
    Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.and_true, Bool.true_and, ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]

open ArmCert.Premises.TranslationAgreesV1

/-- **E17S (candidate E17 v3)**: frame-closed; every permitted access translates with no fault to
    PA {NS, m.pa va}, Normal inner/outer write-back memory, `vaddress = va`, and leaves registers
    and memory unchanged. Events are not constrained (yet). -/
structure E17S (m : ConsumerMap) (s : State) : Prop where
  tr : ∀ u : State, u.regs = s.regs → u.mem = s.mem →
    ∀ va acc aligned size, m.permitted va acc aligned size → ∃ ad t,
      AArch64_TranslateAddress va acc aligned size u = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := m.pa va } ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ ad.vaddress = va ∧
      t.regs = u.regs ∧ t.mem = u.mem

theorem E17S.of_regs {m : ConsumerMap} {s s' : State} (h : E17S m s) (hr : s'.regs = s.regs)
    (hm : s'.mem = s.mem) : E17S m s' :=
  ⟨fun u hu hum => h.tr u (hu.trans hr) (hum.trans hm)⟩

/-- E17S implies the current E17 (TranslationAgrees, frame-closed). -/
theorem E17S.toE17 {m : ConsumerMap} {s : State} (h : E17S m s) :
    ∀ u : State, u.regs = s.regs → u.mem = s.mem → TranslationAgrees m u := by
  intro u hu hum va acc aligned size hp
  rcases h.tr u hu hum va acc aligned size hp with ⟨ad, t, ht, hf, hpa, hmt, _, _, _, hr, hmm⟩
  refine ⟨ad, t, ht, hf, hpa, hmt, ?_, fun a _ => by rw [hmm]⟩
  rw [hr]; exact ProjRegsEq.refl _

/-- The TranslateAddress side packaged for the skeletons. -/
theorem tr_of (m : ConsumerMap) (s : State) (hE : E17S m s) (hP : PostRegs2 s.regs)
    (a : BitVec 64) (acc : AccessDescriptor) (n : Nat) (hp : m.permitted a acc true (n : Int))
    (data : BitVec (n * 8))
    (hmem : ∀ i < n, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = m.pa a ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < n, t1.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      (∃ u, Frame s u ∧ AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
        ad.vaddress = a ∧ t1.regs = s.regs ∧ t1.mem = s.mem) := by
  intro u fu
  rcases hE.tr u fu.1 fu.2.1 a acc true _ hp with ⟨ad, t1, h, hf, hpa, hmt, hin, hout, hv, hr, hm⟩
  have hr' : t1.regs = s.regs := hr.trans fu.1
  have hm' : t1.mem = s.mem := hm.trans fu.2.1
  exact ⟨ad, t1, h, hf, by rw [hpa], hmt, hin, hout, by rw [hr']; exact hP, by rw [hm']; exact hmem,
    u, fu, h, hv, hr', hm'⟩

/-- **LDRB (post-index, tagchecked = TRUE): `Mem_read a 1 acc`** under E17S. MTE is closed by
    FEAT_MTE2 absent (FeatureImpl[134] = false, part of `PostRegs2`; true on fvWitness).
    Value = the PA byte; registers and memory unchanged; events = TranslateAddress's own, then one
    `memRead (m.pa a) 1 (some a) plain/normal false`. -/
theorem readD2_ldrb (m : ConsumerMap) (s : State) (hE : E17S m s) (hP : PostRegs2 s.regs)
    (a : BitVec 64) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : m.permitted a acc true ((1 : Nat) : Int)) (hio : NotMMIO (m.pa a))
    (data : BitVec (1 * 8))
    (hmem : ∀ i < 1, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true ((1 : Nat) : Int) u = .ok ad t1 ∧
      Mem_read a 1 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead (m.pa a).toNat 1 (some a.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  rcases memRead2_1 a acc s (m.pa a) data hA hP.noMTE2 _ (tr_of m s hE hP a acc 1 hp data hmem) hio with
    ⟨ad, t1, t, ⟨u, fu, h1, hv, hr, hm⟩, h, hte, htr, htm⟩
  exact ⟨u, ad, t1, t, fu, h1, h, by rw [hte, kind_eq2 acc hA, hv], htr.trans hr, htm.trans hm⟩

/-- **LDP 64-bit, FEAT_LSE2: `Mem_read__1 a 16 acc true`** (a 16-aligned) under E17S. One 16-byte
    access (inner/outer WB ⇒ single-copy atomic): value = the 16 PA bytes little-endian (low 8 bytes
    = first register), registers and memory unchanged, events = TranslateAddress's own, then ONE
    `memRead (m.pa a) 16 (some a) plain/normal false`. -/
theorem readD2_ldp_lse2 (m : ConsumerMap) (s : State) (hE : E17S m s) (hP : PostRegs2 s.regs)
    (hLSE2 : s.regs.FeatureImpl[111] = true)
    (a : BitVec 64) (halign : a.toNat % 16 = 0) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : m.permitted a acc true ((16 : Nat) : Int)) (hio : NotMMIO (m.pa a))
    (data : BitVec (16 * 8))
    (hmem : ∀ i < 16, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true ((16 : Nat) : Int) u = .ok ad t1 ∧
      Mem_read__1 a 16 acc true s = .ok data t ∧
      t.events = t1.events.push (.memRead (m.pa a).toNat 16 (some a.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  rcases memReadPair a halign acc s (m.pa a) data hA hP.noMTE2 hLSE2 _
      (tr_of m s hE hP a acc 16 hp data hmem) hio with
    ⟨ad, t1, t, ⟨u, fu, h1, hv, hr, hm⟩, h, hte, htr, htm⟩
  exact ⟨u, ad, t1, t, fu, h1, h, by rw [hte, kind_eq2 acc hA, hv], htr.trans hr, htm.trans hm⟩

/-- One aligned 8-byte `Mem_read` under E17S (tagchecked unconstrained, MTE2 absent). -/
theorem read8_E17S (m : ConsumerMap) (s : State) (hE : E17S m s) (hP : PostRegs2 s.regs)
    (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (hA : AccDR acc)
    (hp : m.permitted a acc true ((8 : Nat) : Int)) (hio : NotMMIO (m.pa a))
    (data : BitVec (8 * 8))
    (hmem : ∀ i < 8, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true ((8 : Nat) : Int) u = .ok ad t1 ∧
      Mem_read a 8 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead (m.pa a).toNat 8 (some a.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  have H := MemM1.MemReadD.readD_strong m.pa a 8 (Or.inr rfl) halign acc s data hA hP.post
    (fun u hu hum => by
      rcases hE.tr u hu hum a acc true _ hp with ⟨ad, t1, h, hf, hpa, hmt, _, _, hv, hr, hm⟩
      exact ⟨ad, t1, h, hf, hpa, hmt, hv, hr, hm⟩) hio hmem
  exact H

/-- **LDP 64-bit, no FEAT_LSE2: two `Mem_read _ 8` calls** (at `addInt a 0` then `addInt a 8`, as
    the model's LDP execute does) under E17S. E17S is frame-closed over regs/mem and the first
    read leaves both unchanged, so it applies again. Events: TA₁'s, memRead₁, TA₂'s, memRead₂. -/
theorem readD2_ldp_noLSE2 (m : ConsumerMap) (s : State) (hE : E17S m s) (hP : PostRegs2 s.regs)
    (a : BitVec 64) (acc : AccessDescriptor) (hA : AccDR acc)
    (a0 a8 : BitVec 64) (ha0 : a0 = BitVec.addInt a 0) (ha8 : a8 = BitVec.addInt a 8)
    (h0 : a0.toNat % 8 = 0) (h8 : a8.toNat % 8 = 0)
    (hp0 : m.permitted a0 acc true ((8 : Nat) : Int)) (hp8 : m.permitted a8 acc true ((8 : Nat) : Int))
    (hio0 : NotMMIO (m.pa a0)) (hio8 : NotMMIO (m.pa a8))
    (d1 d2 : BitVec (8 * 8))
    (hm0 : ∀ i < 8, s.mem[(m.pa a0).toNat + i]? = some (d1.extractLsb' (8 * i) 8))
    (hm8 : ∀ i < 8, s.mem[(m.pa a8).toNat + i]? = some (d2.extractLsb' (8 * i) 8)) :
    ∃ t t' u1 ad1 t11 u2 ad2 t21,
      Mem_read (BitVec.addInt a 0) 8 acc s = .ok d1 t ∧
      Mem_read (BitVec.addInt a 8) 8 acc t = .ok d2 t' ∧
      Frame s u1 ∧ AArch64_TranslateAddress a0 acc true ((8 : Nat) : Int) u1 = .ok ad1 t11 ∧
      t.events = t11.events.push (.memRead (m.pa a0).toNat 8 (some a0.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      Frame t u2 ∧ AArch64_TranslateAddress a8 acc true ((8 : Nat) : Int) u2 = .ok ad2 t21 ∧
      t'.events = t21.events.push (.memRead (m.pa a8).toNat 8 (some a8.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      t'.regs = s.regs ∧ t'.mem = s.mem := by
  subst ha0 ha8
  rcases read8_E17S m s hE hP _ h0 acc hA hp0 hio0 d1 hm0 with ⟨u1, ad1, t11, t, fu1, e1, h1, ev1, r1, m1⟩
  rcases read8_E17S m t (hE.of_regs r1 m1) (by rw [r1]; exact hP) _ h8 acc hA hp8 hio8 d2
      (by rw [m1]; exact hm8) with ⟨u2, ad2, t21, t', fu2, e2, h2, ev2, r2, m2⟩
  exact ⟨t, t', u1, ad1, t11, u2, ad2, t21, h1, h2, fu1, e1, ev1, fu2, e2, ev2, r2.trans r1, m2.trans m1⟩

#print axioms mte2_off
#print axioms lse2_on
#print axioms read16
#print axioms single2_1
#print axioms single2_16
#print axioms memRead2_1
#print axioms memReadPair
#print axioms E17S.toE17
#print axioms readD2_ldrb
#print axioms readD2_ldp_lse2
#print axioms readD2_ldp_noLSE2
end MemM1.MemReadD2
