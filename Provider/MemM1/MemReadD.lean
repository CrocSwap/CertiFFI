import MemM1.MemReadIF
import MemM1.MemReadDBE
import BridgeV2.BoundaryV2
import BridgeV2.StateProjectionM
import Pilot.S2Bytes
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open S1Normality MemM1.NoFault MemM1.MemReadIF
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to MemM1.MemReadDLNSym.
namespace MemM1.MemReadD

abbrev State := SequentialState Regs oracleChoiceSource

/-! Data read (`Mem_read a n acc`, n ∈ {1, 8}, aligned) for an EL0 GPR load. -/

theorem align_lit (x : BitVec 64) (y : Nat) (hy : y = 1 ∨ y = 8 ∨ y = 16) :
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
  rcases hy with rfl | rfl | rfl <;> omega

/-- The GPR data-access shape the read path inspects (what `CreateAccDescGPR` returns for a plain
    non-tagchecked, non-transactional, non-exclusive, non-atomic, non-acquire load). -/
structure AccDR (acc : AccessDescriptor) : Prop where
  gpr : acc.acctype = .AccessType_GPR
  tx : acc.transactional = false
  tagchecked : acc.tagchecked = false
  exclusive : acc.exclusive = false
  atomicop : acc.atomicop = false
  acqsc : acc.acqsc = false
  acqpc : acc.acqpc = false
  relsc : acc.relsc = false

/-- Register facts the code AFTER translation reads: `SPESampleInFlight` (SPE sampling hook in
    MemSingle_read) and the `BigEndian` inputs (PSTATE.EL/nRW, the EL2&0 regime bits, SCR_EL3.NS,
    SCTLR_EL2.E0E). None of them is in ProjRegsEq except HCR_EL2. -/
structure PostRegs (r : Regs) : Prop where
  spe : r.bank_Bool .SPESampleInFlight = false
  el0 : r.PSTATE.EL = 0#2
  nrw : r.PSTATE.nRW = 0#1
  noRME : r.FeatureImpl[232] = false
  vhe : r.FeatureImpl[54] = true
  aa64el0 : r.FeatureImpl[4] = true
  ns : Sail.BitVec.extractLsb (r.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1
  e2h : Sail.BitVec.extractLsb (r.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1
  tge : Sail.BitVec.extractLsb (r.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1
  e0e : Sail.BitVec.extractLsb (r.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1

/-- The access kind logged for such a load: a plain, normal-strength explicit access. -/
theorem kind_eq (acc : AccessDescriptor) (hA : AccDR acc) :
    AccessDescriptor_to_Access_kind acc =
      .AK_explicit { variety := .AV_plain, strength := .AS_normal } := by
  unfold AccessDescriptor_to_Access_kind
  rw [hA.gpr]
  simp only [hA.exclusive, hA.atomicop, hA.acqpc, hA.acqsc, hA.relsc, Bool.false_eq_true, ↓reduceIte,
    Bool.or_false]

theorem read1 (address : Nat) (data : BitVec 8) (s : State)
    (h : ∀ i < 1, s.mem[address + i]? = some (data.extractLsb' (8 * i) 8)) :
    (PreSail.readBytes 1 address : SailM (BitVec (8 * 1) × Option Bool)) s = .ok (data, none) s := by
  have h0 := h 0 (by decide)
  simp only [Nat.add_zero, Nat.reduceMul] at h0
  simp [PreSail.readBytes, PreSail.readByte, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, h0]

theorem read8 (address : Nat) (data : BitVec 64) (s : State)
    (h : ∀ i < 8, s.mem[address + i]? = some (data.extractLsb' (8 * i) 8)) :
    (PreSail.readBytes 8 address : SailM (BitVec (8 * 8) × Option Bool)) s = .ok (data, none) s := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h6 := h 6 (by decide)
  have h7 := h 7 (by decide)
  simp only [Nat.add_zero, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  simp [PreSail.readBytes, PreSail.readByte, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, Nat.add_assoc,
    h0, h1, h2, h3, h4, h5, h6, h7, S2Bytes.join64]

theorem constraint_ok (l : ChoiceLabel) (s : State) : ∃ c, undefined_Constraint l () s = .ok c s :=
  ⟨_, rfl⟩

theorem isAligned1 (a : BitVec 64) (h : a.toNat % 1 = 0) : IsAligned__1 a ((1 : Nat) : Int) = true := by
  have hx := align_lit a 1 (by decide)
  unfold IsAligned__1
  rw [hx]
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp
  all_goals omega

theorem allIn1 (a : BitVec 64) (h : a.toNat % 1 = 0) (s : State) :
    AllInAlignedQuantity a ((1 : Nat) : Int) 16 s = .ok true s := by
  have hx : Align_bits (BitVec.subInt (BitVec.addInt a ((1 : Nat) : Int)) 1) (16 : Int) =
      BitVec.ofNat 64 ((BitVec.subInt (BitVec.addInt a ((1 : Nat) : Int)) 1).toNat / 16 * 16) :=
    align_lit _ 16 (by decide)
  have hx' : Align_bits a (16 : Int) = BitVec.ofNat 64 (a.toNat / 16 * 16) := align_lit a 16 (by decide)
  unfold AllInAlignedQuantity
  simp only [ArmFull.assert, PreSail.assert, hx, hx', Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have hlt := a.isLt
  have e : (BitVec.subInt (BitVec.addInt a ((1 : Nat) : Int)) 1).toNat = a.toNat + (1 - 1) := by
    simp [BitVec.subInt, BitVec.addInt, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  rw [e]
  have e2 : (a.toNat + (1 - 1)) / 16 * 16 = a.toNat / 16 * 16 := by omega
  rw [e2]
  simp
  rfl

theorem physRead1 (ad : AddressDescriptor) (acc : AccessDescriptor) (u : State) (data : BitVec (1 * 8))
    (hio : NotMMIO ad.paddress.address)
    (hmem : ∀ i < 1, u.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    PhysMemRead ad 1 acc none u =
      .ok (CreatePhysMemRetStatus .Fault_None, data)
        { u with events := u.events.push (.memRead ad.paddress.address.toNat 1
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
  have hr := read1 ad.paddress.address.toNat data { u with events := (u.events.push (Event.memRead ad.paddress.address.toNat 1 (Option.map (fun x => x.toNat) (some ad.vaddress)) (AccessDescriptor_to_Access_kind acc) false)) } hmem
  simp only [hr]
  rfl

/-- `AArch64_MemSingle_read__1 a 1 acc true false` (aligned, not a pair) skeleton. -/
theorem single1 (a : BitVec 64) (halign : a.toNat % 1 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (1 * 8)) (hA : AccDR acc)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧
      (∀ i < 1, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ AArch64_MemSingle_read__1 a 1 acc true false s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 1 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1631 s with ⟨l1, s1, e1, f1⟩
  rcases bits_normal (Sail.Int.toNatChecked (((1 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have F2 := frame_trans f1 f2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  rcases MemM1.S1T.mte2_normal s2 with ⟨m1, s3, e4, f4⟩
  have F3 := frame_trans F2 f4
  rcases hTA s3 F3 with ⟨ad, t1, e5, hf, hpa, hspe, hm, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  rcases MemM1.S1T.mte2_normal t2 with ⟨m2, t3, e7, f7⟩
  have G3 := frame_trans f6 f7
  have hspe3 : Register.SPESampleInFlight.get t3.regs = false := by rw [G3.1]; exact hspe
  rcases occ_normal 1632 t3 with ⟨l2, t4, e8, f8⟩
  rcases S1EntryCalleesExtra.bool_normal l2 t4 with ⟨b2, t5, e9, f9⟩
  rcases occ_normal 1633 t5 with ⟨l3, t6, e10, f10⟩
  rcases physstat_normal l3 t6 with ⟨ps, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans G3 f8) f9) f10) f11
  have hm7 : ∀ i < 1, t7.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8) := by
    rw [G7.2.1, hpa]; exact hm
  have e12 := physRead1 ad acc t7 data (by rw [hpa]; exact hio) hm7
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned1 a halign
  have hai := allIn1 a halign s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hsz : ((1 : Nat) == 1 || (((1 : Nat) == 2 || (((1 : Nat) == 4 || (((1 : Nat) == 8 || (1 : Nat) == 16))))))) = true := by
    decide
  refine ⟨ad, t1, { t7 with events := t7.events.push (.memRead ad.paddress.address.toNat 1
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind acc) false) }, hQ, ?_, ?_, G7.1, G7.2.1⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_read__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai, hA.tagchecked,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]

/-- `Mem_read a 1 acc` (aligned) skeleton: draws, then exactly the single access. -/
theorem memRead1 (a : BitVec 64) (halign : a.toNat % 1 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (1 * 8)) (hA : AccDR acc)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      PostRegs t1.regs ∧
      (∀ i < 1, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_read a 1 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 1 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((1 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  obtain ⟨lse, e5⟩ : ∃ b, HaveLSE2Ext () s3 = .ok b s3 := ⟨_, rfl⟩
  rcases single1 a halign acc s3 pa data hA (fun ad t1 => Q ad t1 ∧ PostRegs t1.regs)
      (fun u fu => by
        rcases hTA u (frame_trans F3 fu) with ⟨ad, t1, h, hf, hpa, hP, hm, hQ⟩
        exact ⟨ad, t1, h, hf, hpa, hP.spe, hm, hQ, hP⟩) hio with
    ⟨ad, t1, t, ⟨hQ, hP⟩, e6, hte, htr, htm⟩
  have hPt : PostRegs t.regs := htr ▸ hP
  rcases MemM1.MemReadDBE.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hal := isAligned1 a halign
  have hai := allIn1 a halign s3
  have hsz : ((1 : Nat) == 1 || (((1 : Nat) == 2 || (((1 : Nat) == 4 || (((1 : Nat) == 8 || (1 : Nat) == 16))))))) = true := by
    decide
  have hsz2 : (((((1 : Nat) == 1 || (1 : Nat) == 2) || (1 : Nat) == 4) || (1 : Nat) == 8) || (1 : Nat) == 16) = true := by
    decide
  have hasimd : (acc.acctype == AccessType.AccessType_ASIMD) = false := by rw [hA.gpr]; rfl
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  refine ⟨ad, t1, t', hQ, ?_, f7.2.2.trans hte, f7.1.trans htr, f7.2.1.trans htm⟩
  cases lse <;>
  · unfold Mem_read Mem_read__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hsz2, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hasimd, hga, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]

theorem isAligned8 (a : BitVec 64) (h : a.toNat % 8 = 0) : IsAligned__1 a ((8 : Nat) : Int) = true := by
  have hx := align_lit a 8 (by decide)
  unfold IsAligned__1
  rw [hx]
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp
  all_goals omega

theorem allIn8 (a : BitVec 64) (h : a.toNat % 8 = 0) (s : State) :
    AllInAlignedQuantity a ((8 : Nat) : Int) 16 s = .ok true s := by
  have hx : Align_bits (BitVec.subInt (BitVec.addInt a ((8 : Nat) : Int)) 1) (16 : Int) =
      BitVec.ofNat 64 ((BitVec.subInt (BitVec.addInt a ((8 : Nat) : Int)) 1).toNat / 16 * 16) :=
    align_lit _ 16 (by decide)
  have hx' : Align_bits a (16 : Int) = BitVec.ofNat 64 (a.toNat / 16 * 16) := align_lit a 16 (by decide)
  unfold AllInAlignedQuantity
  simp only [ArmFull.assert, PreSail.assert, hx, hx', Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have hlt := a.isLt
  have e : (BitVec.subInt (BitVec.addInt a ((8 : Nat) : Int)) 1).toNat = a.toNat + (8 - 1) := by
    simp [BitVec.subInt, BitVec.addInt, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  rw [e]
  have e2 : (a.toNat + (8 - 1)) / 16 * 16 = a.toNat / 16 * 16 := by omega
  rw [e2]
  simp
  rfl

theorem physRead8 (ad : AddressDescriptor) (acc : AccessDescriptor) (u : State) (data : BitVec (8 * 8))
    (hio : NotMMIO ad.paddress.address)
    (hmem : ∀ i < 8, u.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    PhysMemRead ad 8 acc none u =
      .ok (CreatePhysMemRetStatus .Fault_None, data)
        { u with events := u.events.push (.memRead ad.paddress.address.toNat 8
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
  have hr := read8 ad.paddress.address.toNat data { u with events := (u.events.push (Event.memRead ad.paddress.address.toNat 8 (Option.map (fun x => x.toNat) (some ad.vaddress)) (AccessDescriptor_to_Access_kind acc) false)) } hmem
  simp only [hr]
  rfl

/-- `AArch64_MemSingle_read__1 a 8 acc true false` (aligned, not a pair) skeleton. -/
theorem single8 (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (8 * 8)) (hA : AccDR acc)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ AArch64_MemSingle_read__1 a 8 acc true false s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 8 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1631 s with ⟨l1, s1, e1, f1⟩
  rcases bits_normal (Sail.Int.toNatChecked (((8 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have F2 := frame_trans f1 f2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  rcases MemM1.S1T.mte2_normal s2 with ⟨m1, s3, e4, f4⟩
  have F3 := frame_trans F2 f4
  rcases hTA s3 F3 with ⟨ad, t1, e5, hf, hpa, hspe, hm, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  rcases MemM1.S1T.mte2_normal t2 with ⟨m2, t3, e7, f7⟩
  have G3 := frame_trans f6 f7
  have hspe3 : Register.SPESampleInFlight.get t3.regs = false := by rw [G3.1]; exact hspe
  rcases occ_normal 1632 t3 with ⟨l2, t4, e8, f8⟩
  rcases S1EntryCalleesExtra.bool_normal l2 t4 with ⟨b2, t5, e9, f9⟩
  rcases occ_normal 1633 t5 with ⟨l3, t6, e10, f10⟩
  rcases physstat_normal l3 t6 with ⟨ps, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans G3 f8) f9) f10) f11
  have hm7 : ∀ i < 8, t7.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8) := by
    rw [G7.2.1, hpa]; exact hm
  have e12 := physRead8 ad acc t7 data (by rw [hpa]; exact hio) hm7
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned8 a halign
  have hai := allIn8 a halign s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hsz : ((8 : Nat) == 1 || (((8 : Nat) == 2 || (((8 : Nat) == 4 || (((8 : Nat) == 8 || (8 : Nat) == 16))))))) = true := by
    decide
  refine ⟨ad, t1, { t7 with events := t7.events.push (.memRead ad.paddress.address.toNat 8
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind acc) false) }, hQ, ?_, ?_, G7.1, G7.2.1⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa]
  cases lse <;> cases tme <;>
  · unfold AArch64_MemSingle_read__1
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hnn, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai, hA.tagchecked,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false, Sail.BitVec.castWidth_eq]

/-- `Mem_read a 8 acc` (aligned) skeleton: draws, then exactly the single access. -/
theorem memRead8 (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (8 * 8)) (hA : AccDR acc)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      PostRegs t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_read a 8 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 8 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((8 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  obtain ⟨lse, e5⟩ : ∃ b, HaveLSE2Ext () s3 = .ok b s3 := ⟨_, rfl⟩
  rcases single8 a halign acc s3 pa data hA (fun ad t1 => Q ad t1 ∧ PostRegs t1.regs)
      (fun u fu => by
        rcases hTA u (frame_trans F3 fu) with ⟨ad, t1, h, hf, hpa, hP, hm, hQ⟩
        exact ⟨ad, t1, h, hf, hpa, hP.spe, hm, hQ, hP⟩) hio with
    ⟨ad, t1, t, ⟨hQ, hP⟩, e6, hte, htr, htm⟩
  have hPt : PostRegs t.regs := htr ▸ hP
  rcases MemM1.MemReadDBE.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hal := isAligned8 a halign
  have hai := allIn8 a halign s3
  have hsz : ((8 : Nat) == 1 || (((8 : Nat) == 2 || (((8 : Nat) == 4 || (((8 : Nat) == 8 || (8 : Nat) == 16))))))) = true := by
    decide
  have hsz2 : (((((8 : Nat) == 1 || (8 : Nat) == 2) || (8 : Nat) == 4) || (8 : Nat) == 8) || (8 : Nat) == 16) = true := by
    decide
  have hasimd : (acc.acctype == AccessType.AccessType_ASIMD) = false := by rw [hA.gpr]; rfl
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  refine ⟨ad, t1, t', hQ, ?_, f7.2.2.trans hte, f7.1.trans htr, f7.2.1.trans htm⟩
  cases lse <;>
  · unfold Mem_read Mem_read__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz, hsz2, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hasimd, hga, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]

/-- The `n` PA bytes of a permitted access are not table bytes (MapOK.contiguous + tableDisjoint). -/
theorem notTable (m : ConsumerMap) (hM : MapOK m) (a : BitVec 64) (acc : AccessDescriptor)
    (aligned : Bool) (n : Nat) (hp : m.permitted a acc aligned (n : Int)) :
    ∀ i < n, ¬ m.tableByte ((m.pa a).toNat + i) := by
  intro i hi
  have hc := hM.contiguous a acc aligned n i hp (by omega)
  rw [← hc]
  exact hM.tableDisjoint _ ⟨a, acc, aligned, n, i, hp, by omega, rfl⟩

/-- **Data read under the abstract boundary premise E17** (frame-closed `TranslationAgrees`), for
    `Mem_read a n acc` with n ∈ {1, 8}, `a` n-aligned. `hPost` is what E17 does not give but the
    post-translation code reads: `PostRegs` of the register file the actual TranslateAddress
    returns (SPESampleInFlight; BigEndian's PSTATE.EL/nRW, regime bits, SCR_EL3.NS, SCTLR_EL2.E0E). The value is the n PA bytes little-endian; registers agree on the
    projection; memory agrees off table bytes; events are TranslateAddress's own (abstract: E17 says
    nothing about them) followed by exactly one data `memRead` whose va field is the descriptor's
    `vaddress` (E17 does not pin it either). -/
theorem readD_E17 (m : ConsumerMap) (hM : MapOK m) (a : BitVec 64) (n : Nat) (hn : n = 1 ∨ n = 8)
    (halign : a.toNat % n = 0) (acc : AccessDescriptor) (s : State) (data : BitVec (n * 8))
    (hA : AccDR acc)
    (hE : ∀ u : State, u.regs = s.regs → u.mem = s.mem → TranslationAgrees m u)
    (hp : m.permitted a acc true (n : Int))
    (hPost : ∀ u ad t1, u.regs = s.regs → u.mem = s.mem →
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 → PostRegs t1.regs)
    (hio : NotMMIO (m.pa a))
    (hmem : ∀ i < n, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := m.pa a } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      Mem_read a n acc s = .ok data t ∧
      t.events = t1.events.push (.memRead (m.pa a).toNat n (some ad.vaddress.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      ProjRegsEq s.regs t.regs ∧ (∀ x, ¬ m.tableByte x → t.mem[x]? = s.mem[x]?) := by
  have hnt := notTable m hM a acc true n hp
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame s u ∧
    AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧
    ad.paddress = { paspace := .PAS_NonSecure, address := m.pa a } ∧
    ad.memattrs.memtype = .MemType_Normal ∧
    ProjRegsEq s.regs t1.regs ∧ (∀ x, ¬ m.tableByte x → t1.mem[x]? = s.mem[x]?)
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = m.pa a ∧
      PostRegs t1.regs ∧
      (∀ i < n, t1.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1 := by
    intro u fu
    rcases hE u fu.1 fu.2.1 a acc true _ hp with ⟨ad, t1, h, hf, hpa, hmt, hpr, hmm⟩
    have hmm' : ∀ x, ¬ m.tableByte x → t1.mem[x]? = s.mem[x]? := fun x hx => (hmm x hx).trans (by rw [fu.2.1])
    refine ⟨ad, t1, h, hf, by rw [hpa], hPost u ad t1 fu.1 fu.2.1 h,
      fun i hi => (hmm' _ (hnt i hi)).trans (hmem i hi), u, fu, h, hf, hpa, hmt, ?_, hmm'⟩
    rw [← fu.1]; exact hpr
  rcases hn with rfl | rfl
  · rcases memRead1 a halign acc s (m.pa a) data hA Q hTA hio with
      ⟨ad, t1, t, ⟨u, fu, h1, hf, hpa, hmt, hpr, hmm⟩, h, hte, htr, htm⟩
    refine ⟨u, ad, t1, t, fu, h1, hf, hpa, hmt, h, by rw [hte, kind_eq acc hA], by rw [htr]; exact hpr,
      fun x hx => by rw [htm]; exact hmm x hx⟩
  · rcases memRead8 a halign acc s (m.pa a) data hA Q hTA hio with
      ⟨ad, t1, t, ⟨u, fu, h1, hf, hpa, hmt, hpr, hmm⟩, h, hte, htr, htm⟩
    refine ⟨u, ad, t1, t, fu, h1, hf, hpa, hmt, h, by rw [hte, kind_eq acc hA], by rw [htr]; exact hpr,
      fun x hx => by rw [htm]; exact hmm x hx⟩

/-- **Data read under the strengthened premise hE'** (TranslateAddress on any state with `s`'s
    registers and memory keeps registers and memory, returns `vaddress = a`; memory's coreV/agreesK
    supply this), plus `SPESampleInFlight = false` on `s`. Then registers and memory are unchanged
    and the data event's va field is `a`. -/
theorem readD_strong (pa : BitVec 64 → BitVec 56) (a : BitVec 64) (n : Nat) (hn : n = 1 ∨ n = 8)
    (halign : a.toNat % n = 0) (acc : AccessDescriptor) (s : State) (data : BitVec (n * 8))
    (hA : AccDR acc) (hP : PostRegs s.regs)
    (hE' : ∀ u : State, u.regs = s.regs → u.mem = s.mem → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := pa a } ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.vaddress = a ∧
      t1.regs = u.regs ∧ t1.mem = u.mem)
    (hio : NotMMIO (pa a))
    (hmem : ∀ i < n, s.mem[(pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      Mem_read a n acc s = .ok data t ∧
      t.events = t1.events.push (.memRead (pa a).toNat n (some a.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame s u ∧
    AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧ ad.vaddress = a ∧
    t1.regs = s.regs ∧ t1.mem = s.mem
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa a ∧
      PostRegs t1.regs ∧
      (∀ i < n, t1.mem[(pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1 := by
    intro u fu
    rcases hE' u fu.1 fu.2.1 with ⟨ad, t1, h, hf, hpa, hmt, hv, hr, hm⟩
    have hr' : t1.regs = s.regs := hr.trans fu.1
    have hm' : t1.mem = s.mem := hm.trans fu.2.1
    exact ⟨ad, t1, h, hf, by rw [hpa], by rw [hr']; exact hP, by rw [hm']; exact hmem,
      u, fu, h, hv, hr', hm'⟩
  rcases hn with rfl | rfl
  · rcases memRead1 a halign acc s (pa a) data hA Q hTA hio with
      ⟨ad, t1, t, ⟨u, fu, h1, hv, hr, hm⟩, h, hte, htr, htm⟩
    exact ⟨u, ad, t1, t, fu, h1, h, by rw [hte, kind_eq acc hA, hv], htr.trans hr, htm.trans hm⟩
  · rcases memRead8 a halign acc s (pa a) data hA Q hTA hio with
      ⟨ad, t1, t, ⟨u, fu, h1, hv, hr, hm⟩, h, hte, htr, htm⟩
    exact ⟨u, ad, t1, t, fu, h1, h, by rw [hte, kind_eq acc hA, hv], htr.trans hr, htm.trans hm⟩

end MemM1.MemReadD

