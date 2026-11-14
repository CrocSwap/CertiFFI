import MemM1.M1CoreIFE
import MemM1.AccIF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemReadIF
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.WitnessIF MemM1.WitnessIFE

/-! ### Alignment (the `IsAligned` / `AllInAlignedQuantity` asserts of MemSingle_read). -/
theorem align_lit (x : BitVec 64) (y : Nat) (hy : y = 4 ∨ y = 16) :
    Align_bits x (y : Int) = BitVec.ofNat 64 (x.toNat / y * y) := by
  unfold Align_bits Align_int fdiv_int Slice_int get_slice_int
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.castWidth_eq, Sail.BitVec.toNatInt]
  have hlt := x.isLt
  split
  · next h => exact absurd (of_decide_eq_true h.1) (by simp)
  split
  · next h => omega
  rw [show (BitVec.length x + 1) = 65 from rfl]
  rcases hy with rfl | rfl <;> omega

theorem isAligned4 (pc : BitVec 64) (hpc : pc.toNat % 4 = 0) : IsAligned__1 pc ((4 : Nat) : Int) = true := by
  have h := align_lit pc 4 (Or.inl rfl)
  unfold IsAligned__1
  rw [h]
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem allIn16 (pc : BitVec 64) (hpc : pc.toNat % 4 = 0) (s : State) :
    AllInAlignedQuantity pc ((4 : Nat) : Int) 16 s = .ok true s := by
  have h : Align_bits (BitVec.subInt (BitVec.addInt pc ((4 : Nat) : Int)) 1) (16 : Int) =
      BitVec.ofNat 64 ((BitVec.subInt (BitVec.addInt pc ((4 : Nat) : Int)) 1).toNat / 16 * 16) :=
    align_lit _ 16 (Or.inr rfl)
  have h' : Align_bits pc (16 : Int) = BitVec.ofNat 64 (pc.toNat / 16 * 16) := align_lit pc 16 (Or.inr rfl)
  unfold AllInAlignedQuantity
  simp only [ArmFull.assert, PreSail.assert, h, h', Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have hlt := pc.isLt
  have e : (BitVec.subInt (BitVec.addInt pc ((4 : Nat) : Int)) 1).toNat = pc.toNat + 3 := by
    simp [BitVec.subInt, BitVec.addInt, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  rw [e]
  have e2 : (pc.toNat + 3) / 16 * 16 = pc.toNat / 16 * 16 := by omega
  rw [e2]
  simp
  rfl

/-! ### The 4-byte RAM read (little-endian: byte at `pa + i` is bits `8i+7 .. 8i`). -/
theorem join32 (d : BitVec 32) :
    BitVec.append (BitVec.append (BitVec.append (d.extractLsb' 24 8) (d.extractLsb' 16 8))
      (d.extractLsb' 8 8)) (d.extractLsb' 0 8) = d := by
  simp only [BitVec.append_eq]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 8) (by decide : 24 = 16 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 16) (by decide : 16 = 8 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 24) (by decide : 8 = 0 + 8)]
  exact BitVec.extractLsb'_eq_self

theorem join32' (d : BitVec 32) :
    d.extractLsb' 24 8 +++ d.extractLsb' 16 8 +++ d.extractLsb' 8 8 +++ d.extractLsb' 0 8 = d := by
  simpa only [BitVec.append_eq] using join32 d

theorem read4 (address : Nat) (data : BitVec 32) (s : State)
    (h : ∀ i < 4, s.mem[address + i]? = some (data.extractLsb' (8 * i) 8)) :
    (PreSail.readBytes 4 address : SailM (BitVec (8 * 4) × Option Bool)) s = .ok (data, none) s := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.add_zero, Nat.reduceMul] at h0 h1 h2 h3
  simp [PreSail.readBytes, PreSail.readByte, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, Nat.add_assoc, h0, h1, h2, h3, join32']

/-- The physical address is not in the model's GIC (0x2C00xxxx) or UART (0x3C00xxxx) 64 KiB
    page, which `PhysMemRead` special-cases. -/
def NotMMIO (pa : BitVec 56) : Prop :=
  Sail.BitVec.extractLsb pa 55 16 ≠ 0x2C00#40 ∧ Sail.BitVec.extractLsb pa 55 16 ≠ 0x3C00#40

/-- `PhysMemRead` of 4 RAM bytes: one `memRead` event, value = the 4 bytes little-endian. -/
theorem physRead (ad : AddressDescriptor) (acc : AccessDescriptor) (u : State) (data : BitVec 32)
    (hio : NotMMIO ad.paddress.address)
    (hmem : ∀ i < 4, u.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    PhysMemRead ad 4 acc none u =
      .ok (CreatePhysMemRetStatus .Fault_None, data)
        { u with events := u.events.push (.memRead ad.paddress.address.toNat 4
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
    Pure.pure, EStateM.pure, ArmFull.ConcurrencyInterfaceV1.sail_mem_read, PreSail.sail_mem_read, PreSail.logEvent, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, read_request]
  have hr := read4 ad.paddress.address.toNat data { u with events := (u.events.push (Event.memRead ad.paddress.address.toNat 4 (Option.map (fun x => x.toNat) (some ad.vaddress)) (AccessDescriptor_to_Access_kind acc) false)) } hmem
  simp only [hr]
  rfl

theorem physstat_normal (l : ChoiceLabel) : Normal (undefined_PhysMemRetStatus l ()) := by
  intro s
  unfold undefined_PhysMemRetStatus
  obtain ⟨f0, e0⟩ : ∃ f, undefined_Fault (l.child 0) () s = .ok f s := ⟨_, rfl⟩
  rcases bits_normal 1 (l.child 1) s with ⟨b1, s1, e1, f1⟩
  obtain ⟨m2, e2⟩ : ∃ m, undefined_ErrorState (l.child 2) () s1 = .ok m s1 := ⟨_, rfl⟩
  rcases bits_normal 64 (l.child 3) s1 with ⟨b3, s3, e3, f3⟩
  exact ⟨{ statuscode := f0, extflag := b1, merrorstate := m2, store64bstatus := b3 }, s3,
    by simp only [Bind.bind, EStateM.bind, e0, e1, e2, e3, Pure.pure, EStateM.pure], frame_trans f1 f3⟩

/-- The instruction-fetch access shape used by MemSingle_read: `AccIF` plus the flags its
    tag-check and atomicity tests read (all false in what `CreateAccDescIFetch` returns). -/
structure AccIFR (acc : AccessDescriptor) : Prop where
  base : AccIF acc
  tagchecked : acc.tagchecked = false
  exclusive : acc.exclusive = false
  atomicop : acc.atomicop = false
  acqsc : acc.acqsc = false
  acqpc : acc.acqpc = false
  relsc : acc.relsc = false

theorem nad_more (s : State) (acc : AccessDescriptor) (t : State)
    (h : MemM1.AccIF.nad_native s = .ok acc t) :
    acc.tagchecked = false ∧ acc.exclusive = false ∧ acc.atomicop = false ∧
      acc.acqsc = false ∧ acc.acqpc = false ∧ acc.relsc = false := by
  delta MemM1.AccIF.nad_native at h
  injection h with ha ht
  subst ha
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `AccIF.create` strengthened: the actual `CreateAccDescIFetch ()` at EL0 returns an `AccIFR`. -/
theorem createR (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    ∃ acc t, CreateAccDescIFetch () s = .ok acc t ∧ AccIFR acc ∧ Frame s t := by
  rcases MemM1.AccIF.create s hNoRME hA64 hEL3A64 hNoEL3A32 hEL hNS with
    ⟨acc, t, hc, hA, _, _, _, _, _, f⟩
  have hn : MemM1.AccIF.nad_native s = .ok acc t :=
    (MemM1.AccIF.nad_eq s hNoRME hA64 hEL3A64 hNoEL3A32 hEL).symm.trans hc
  rcases nad_more s acc t hn with ⟨a1, a2, a3, a4, a5, a6⟩
  exact ⟨acc, t, hc, ⟨hA, a1, a2, a3, a4, a5, a6⟩, f⟩

/-- MemSingle_read skeleton: `AArch64_MemSingle_read pc 4 acc true` for an IFETCH access at a
    4-aligned `pc`, given what TranslateAddress returns on any framed state. -/
theorem read_skel (pc : BitVec 64) (hpc : pc.toNat % 4 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec 32) (hA : AccIFR acc)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress pc acc true ((4 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧ ad.vaddress = pc ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ t1.mem = s.mem ∧ Q ad t1)
    (hio : NotMMIO pa)
    (hmem : ∀ i < 4, s.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad t1 t, Q ad t1 ∧ AArch64_MemSingle_read pc 4 acc true s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 4 (some pc.toNat) (AK_ifetch ()) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1631 s with ⟨l1, s1, e1, f1⟩
  rcases bits_normal (Sail.Int.toNatChecked (((4 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have F2 := frame_trans f1 f2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  rcases MemM1.S1T.mte2_normal s2 with ⟨m1, s3, e4, f4⟩
  have F3 := frame_trans F2 f4
  rcases hTA s3 F3 with ⟨ad, t1, e5, hf, hpa, hva, hspe, hm, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  rcases MemM1.S1T.mte2_normal t2 with ⟨m2, t3, e7, f7⟩
  have G3 := frame_trans f6 f7
  have hspe3 : Register.SPESampleInFlight.get t3.regs = false := by rw [G3.1]; exact hspe
  rcases occ_normal 1632 t3 with ⟨l2, t4, e8, f8⟩
  rcases S1EntryCalleesExtra.bool_normal l2 t4 with ⟨b2, t5, e9, f9⟩
  rcases occ_normal 1633 t5 with ⟨l3, t6, e10, f10⟩
  rcases physstat_normal l3 t6 with ⟨ps, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans G3 f8) f9) f10) f11
  have hm7 : ∀ i < 4, t7.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8) := by
    rw [G7.2.1, hm, hpa]; exact hmem
  have e12 := physRead ad acc t7 data (by rw [hpa]; exact hio) hm7
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned4 pc hpc
  have hai := allIn16 pc hpc s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hsz : ((4 : Nat) == 1 || ((4 : Nat) == 2 || ((4 : Nat) == 4 || ((4 : Nat) == 8 || (4 : Nat) == 16)))) = true := by
    decide
  refine ⟨ad, t1, { t7 with events := t7.events.push (.memRead ad.paddress.address.toNat 4
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind acc) false) }, hQ, ?_, ?_, G7.1, G7.2.1⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa, hva]
    unfold AccessDescriptor_to_Access_kind
    rw [hA.base.ifetch]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_read AArch64_MemSingle_read__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai, hA.tagchecked,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.base.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]
    done

/-- `WitnessIF.coreIF` plus `ad.vaddress = va` (no event tracking). M1 core, instruction fetch: the actual AArch64_TranslateAddress at a lower-range `va` for an
    EL0 NS IFETCH access. The only register effect is the model's `SetInGuardedPage false`
    (the leaf has GP = 0), so the final registers are `clrGP s.regs`. -/
theorem coreIFV (va : BitVec 64) (hva : va.toNat < 2^48) (B : BitVec 56)
    (hB : B &&& 0xfff#56 = 0#56) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (hR : Witness.Regs20 s.regs) (hA : AccIF acc) (hW : WalkOKIF acc s va B) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.vaddress = va ∧
      t.regs = MemM1.IF.clrGP s.regs ∧ t.mem = s.mem := by
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
  have h3 := translateIFE va acc aligned size s .Regime_EL20 s0 ti s1 ad t df t2 hA.ifetch h0 h1 hfull hadf
      (MemM1.Callees.rme t (by rw [htr]; exact hR.noRME)) hdbg
  exact ⟨_, _, h3, hdf, hpa, hmt, by show Sail.BitVec.zeroExtend va 64 = va; simp [Sail.BitVec.zeroExtend],
    f2.1.trans htr, f2.2.1.trans htm⟩

#print axioms coreIFV

theorem walkOKIFE_transport (acc : AccessDescriptor) (s s' : State) (va : BitVec 64) (B : BitVec 56)
    (W : Array Event) (hr : s'.regs = s.regs) (hm : s'.mem = s.mem) (h : WalkOKIFE acc s va B W) :
    WalkOKIFE acc s' va B W := by
  unfold WalkOKIFE at *
  rw [hr, hm]
  exact h

theorem walkOKIF_transport (acc : AccessDescriptor) (s s' : State) (va : BitVec 64) (B : BitVec 56)
    (hr : s'.regs = s.regs) (hm : s'.mem = s.mem) (h : WalkOKIF acc s va B) : WalkOKIF acc s' va B := by
  unfold WalkOKIF at *
  rw [hr, hm]
  exact h

theorem spe_clrGP (R : Regs) (h : R.bank_Bool .SPESampleInFlight = false) :
    (MemM1.IF.clrGP R).bank_Bool .SPESampleInFlight = false := by
  show RegMap.set R.bank_Bool Bank_Bool.InGuardedPage false Bank_Bool.SPESampleInFlight = false
  rw [RegMap.set_ne _ _ (by decide)]
  exact h

theorem ev_shape2 (a b W : Array Event) (x y : Event) :
    (a ++ (b ++ W ++ #[x])).push y = a ++ (b ++ W ++ #[x, y]) := by
  rw [Array.push_eq_append]
  simp only [Array.append_assoc]
  rfl

/-- **M-b, event-exact.** The actual `AArch64_MemSingle_read pc 4 acc true` (the call `__FetchInstr`
    makes on AArch64) for an EL0 NS instruction fetch at a 4-aligned lower-range `pc`, on a state
    where `coreIF`'s hypotheses hold and the walk appends exactly `W`: returns the 4 bytes at
    PA {NS, pageOA B pc} little-endian (byte at `pa + i` = bits `8i+7..8i`; MemSingle_read applies
    no endianness reversal), memory unchanged, registers `clrGP s.regs`, and the event log grows by
    exactly `translationStart ti, W, translationEnd ad, memRead pa 4 (some pc) ifetch (tag false)`. -/
theorem read_exact (pc : BitVec 64) (hpc : pc.toNat % 4 = 0) (hva : pc.toNat < 2^48)
    (B : BitVec 56) (hB : B &&& 0xfff#56 = 0#56) (acc : AccessDescriptor) (s : State) (W : Array Event)
    (hR : Witness.Regs20 s.regs) (hA : AccIFR acc) (hW : WalkOKIFE acc s pc B W)
    (data : BitVec 32) (hio : NotMMIO (MemM1.VA.pageOA B pc))
    (hmem : ∀ i < 4, s.mem[(MemM1.VA.pageOA B pc).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ti ad t, AArch64_MemSingle_read pc 4 acc true s = .ok data t ∧
      t.events = s.events ++ (#[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad,
          Event.memRead (MemM1.VA.pageOA B pc).toNat 4 (some pc.toNat) (AK_ifetch ()) false]) ∧
      t.mem = s.mem ∧ t.regs = MemM1.IF.clrGP s.regs ∧
      TSIOK ti acc pc ((4 : Nat) : Int) s ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B pc} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.vaddress = pc := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ ti,
    t1.events = s.events ++ (#[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad]) ∧
    t1.regs = MemM1.IF.clrGP s.regs ∧ TSIOK ti acc pc ((4 : Nat) : Int) s ∧
    ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B pc} ∧
    ad.memattrs.memtype = .MemType_Normal ∧ ad.fault.statuscode = .Fault_None ∧
    ad.vaddress = pc ∧ t1.mem = s.mem
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress pc acc true ((4 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = MemM1.VA.pageOA B pc ∧ ad.vaddress = pc ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ t1.mem = s.mem ∧ Q ad t1 := by
    intro u fu
    rcases MemM1.WitnessIFE.coreIFE pc hva B hB acc true ((4 : Nat) : Int) u W (by rw [fu.1]; exact hR)
        hA.base (walkOKIFE_transport acc s u pc B W fu.1 fu.2.1 hW) with
      ⟨ti, ad, t1, h, hf, hpa, hmt, hv, hr, hm, he, q1, q2, q3, q4, q5, u0, u0', fu0, hg⟩
    have hr' : t1.regs = MemM1.IF.clrGP s.regs := by rw [hr, fu.1]
    refine ⟨ad, t1, h, hf, by rw [hpa], hv, by rw [hr']; exact spe_clrGP _ hR.spe, hm.trans fu.2.1,
      ti, by rw [he, fu.2.2], hr', ⟨q1, q2, q3, q4, q5, u0, u0', frame_trans fu fu0, hg⟩, hpa, hmt, hf, hv,
      hm.trans fu.2.1⟩
  rcases read_skel pc hpc acc s _ data hA Q hTA hio hmem with
    ⟨ad, t1, t, ⟨ti, he, hr, hti, hpa, hmt, hf, hv, hm⟩, h, hte, htr, htm⟩
  refine ⟨ti, ad, t, h, ?_, htm.trans hm, htr.trans hr, hti, hf, hpa, hmt, hv⟩
  rw [hte, he, ev_shape2]

/-- **M-b, relative to TranslateAddress (no walk-event hypothesis).** Same read, with the event log
    stated relative to the TranslateAddress call it makes: MemSingle_read first only draws
    choice bookkeeping (state `u`, framed), then runs the actual TranslateAddress (result `ad`,
    state `t1`), then appends exactly one `memRead` event. -/
theorem read_rel (pc : BitVec 64) (hpc : pc.toNat % 4 = 0) (hva : pc.toNat < 2^48)
    (B : BitVec 56) (hB : B &&& 0xfff#56 = 0#56) (acc : AccessDescriptor) (s : State)
    (hR : Witness.Regs20 s.regs) (hA : AccIFR acc) (hW : WalkOKIF acc s pc B)
    (data : BitVec 32) (hio : NotMMIO (MemM1.VA.pageOA B pc))
    (hmem : ∀ i < 4, s.mem[(MemM1.VA.pageOA B pc).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress pc acc true ((4 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B pc} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.vaddress = pc ∧
      AArch64_MemSingle_read pc 4 acc true s = .ok data t ∧
      t.events = t1.events.push
        (Event.memRead (MemM1.VA.pageOA B pc).toNat 4 (some pc.toNat) (AK_ifetch ()) false) ∧
      t.mem = s.mem ∧ t.regs = MemM1.IF.clrGP s.regs := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame s u ∧
    AArch64_TranslateAddress pc acc true ((4 : Nat) : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧
    ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B pc} ∧
    ad.memattrs.memtype = .MemType_Normal ∧ ad.vaddress = pc ∧
    t1.regs = MemM1.IF.clrGP s.regs ∧ t1.mem = s.mem
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress pc acc true ((4 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = MemM1.VA.pageOA B pc ∧ ad.vaddress = pc ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ t1.mem = s.mem ∧ Q ad t1 := by
    intro u fu
    rcases coreIFV pc hva B hB acc true ((4 : Nat) : Int) u (by rw [fu.1]; exact hR) hA.base
        (walkOKIF_transport acc s u pc B fu.1 fu.2.1 hW) with
      ⟨ad, t1, h, hf, hpa, hmt, hv, hr, hm⟩
    have hr' : t1.regs = MemM1.IF.clrGP s.regs := by rw [hr, fu.1]
    exact ⟨ad, t1, h, hf, by rw [hpa], hv, by rw [hr']; exact spe_clrGP _ hR.spe, hm.trans fu.2.1,
      u, fu, h, hf, hpa, hmt, hv, hr', hm.trans fu.2.1⟩
  rcases read_skel pc hpc acc s _ data hA Q hTA hio hmem with
    ⟨ad, t1, t, ⟨u, fu, h1, hf, hpa, hmt, hv, hr, hm⟩, h, hte, htr, htm⟩
  exact ⟨u, ad, t1, t, fu, h1, hf, hpa, hmt, hv, h, hte, htm.trans hm, htr.trans hr⟩

#print axioms read_rel
#print axioms read_skel
#print axioms createR
#print axioms read_exact
end MemM1.MemReadIF
