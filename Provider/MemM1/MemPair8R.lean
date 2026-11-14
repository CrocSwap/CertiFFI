import MemM1.MemDataV5
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemPair8R
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2 MemM1.MemWriteD1

/-! LDP / STP 64-bit pair (`Mem_read__1 a 16 acc true` / `Mem_set__1 a 16 acc true v`) with FEAT_LSE2
at an address that is 8-aligned but NOT 16-aligned. In `Mem_read__2` / `Mem_set__2`:
`aligned = IsAligned a 8 = true` (so no `AArch64_UnalignedAccessFaults` / SCTLR.A check),
`AllInAlignedQuantity a 16 16 = false`, hence the `ispair && aligned` branch: TWO single-copy
8-byte accesses (`MemSingle_*__1 _ 8 acc true false`), at `a` then `addInt a 8`, each with its own
TranslateAddress (size 8, aligned = true). -/

/-- The 16-byte pair at an 8- but not 16-aligned address straddles a 16-byte boundary. -/
theorem allIn16_false (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0) (s : State) :
    AllInAlignedQuantity a ((16 : Nat) : Int) 16 s = .ok false s := by
  have h : Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) (16 : Int) =
      BitVec.ofNat 64 ((BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1).toNat / 16 * 16) := align16 _
  have h' := align16 a
  have hle : (((16 : Nat) : Int) ≤b 16) = true := by decide
  unfold AllInAlignedQuantity
  simp only [ArmFull.assert, PreSail.assert, h, h', hle, Bind.bind, EStateM.bind, Pure.pure,
    EStateM.pure, ↓reduceIte]
  have hlt := a.isLt
  have e : (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1).toNat = (a.toNat + 15) % 2 ^ 64 := by
    simp [BitVec.subInt, BitVec.addInt, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  rw [e]
  have hne : (BitVec.ofNat 64 ((a.toNat + 15) % 2 ^ 64 / 16 * 16) == BitVec.ofNat 64 (a.toNat / 16 * 16)) = false := by
    rw [beq_eq_false_iff_ne]
    intro hq
    have := congrArg BitVec.toNat hq
    simp only [BitVec.toNat_ofNat] at this
    omega
  all_goals rw [hne]

/-- The second half's address `addInt a 8` is `a + 8`. -/
theorem addInt8 (a : BitVec 64) : BitVec.addInt a ((8 : Nat) : Int) = a + 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.addInt, BitVec.toNat_add]

/-- Byte `i` of the low / high 8-byte half of a 16-byte value. -/
theorem lo_byte (data : BitVec 128) (i : Nat) (hi : i < 8) :
    (data.extractLsb' 0 64).extractLsb' (8 * i) 8 = data.extractLsb' (8 * i) 8 := by
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega)]
  all_goals simp

theorem hi_byte (data : BitVec 128) (i : Nat) (hi : i < 8) :
    (data.extractLsb' 64 64).extractLsb' (8 * i) 8 = data.extractLsb' (8 * (i + 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  have h1 : 8 * i + j < 64 := by omega
  have h2 : 64 + (8 * i + j) = 8 * (i + 8) + j := by omega
  simp [hj, h1, h2]

theorem cw_toNat {n m : Nat} (x : BitVec n) (h : n = m) :
    (Sail.BitVec.castWidth (m := m) x).toNat = x.toNat := by
  subst h
  simp

theorem join_toNat (data : BitVec 128) :
    (data.extractLsb' 64 64 ++ data.extractLsb' 0 64).toNat = data.toNat := by
  have e := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := data) (start₁ := 0)
    (len₁ := 64) (start₂ := 64) (len₂ := 64) rfl
  rw [e]
  have := data.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt this

/-- The strong per-access translation premise (E17 v3's data clauses, events left to the caller). -/
def TAS (b : BitVec 64) (acc : AccessDescriptor) (pa : BitVec 56) (s : State) : Prop :=
  ∀ u : State, u.regs = s.regs → u.mem = s.mem → ∃ ad t1,
    AArch64_TranslateAddress b acc true ((8 : Nat) : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
    ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
    ad.memattrs.outer.attrs = MemAttr_WB ∧ ad.vaddress = b ∧ t1.regs = u.regs ∧ t1.mem = u.mem

/-- One 8-byte half under TAS on a state with `s`'s registers and memory. -/
theorem half_read (b : BitVec 64) (hb : b.toNat % 8 = 0) (acc : AccessDescriptor) (s x : State)
    (pa : BitVec 56) (d : BitVec (8 * 8)) (hA : AccDR2 acc) (hP : PostRegs2 s.regs)
    (hE : TAS b acc pa s) (hio : NotMMIO pa) (hxr : x.regs = s.regs) (hxm : x.mem = s.mem)
    (hmem : ∀ i < 8, s.mem[pa.toNat + i]? = some (d.extractLsb' (8 * i) 8)) :
    ∃ u ad t1 y, Frame x u ∧ AArch64_TranslateAddress b acc true ((8 : Nat) : Int) u = .ok ad t1 ∧
      AArch64_MemSingle_read__1 b 8 acc true false x = .ok d y ∧
      y.events = t1.events.push (.memRead pa.toNat 8 (some b.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      y.regs = s.regs ∧ y.mem = s.mem := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame x u ∧
    AArch64_TranslateAddress b acc true ((8 : Nat) : Int) u = .ok ad t1 ∧ ad.vaddress = b ∧
    t1.regs = s.regs ∧ t1.mem = s.mem
  rcases single2_8 b hb acc x pa d hA (by rw [hxr]; exact hP.noMTE2) Q
      (fun u fu => by
        rcases hE u (fu.1.trans hxr) (fu.2.1.trans hxm) with
          ⟨ad, t1, h, hf, hpa, hmt, hin, hout, hv, hr, hm⟩
        have hr' : t1.regs = s.regs := hr.trans (fu.1.trans hxr)
        have hm' : t1.mem = s.mem := hm.trans (fu.2.1.trans hxm)
        exact ⟨ad, t1, h, hf, hpa, hmt, hin, hout, by rw [hr']; exact hP, by rw [hm']; exact hmem,
          u, fu, h, hv, hr', hm'⟩) hio with
    ⟨ad, t1, y, ⟨u, fu, h1, hv, hr, hm⟩, _, hy, hev, hyr, hym⟩
  exact ⟨u, ad, t1, y, fu, h1, hy, by rw [hev, kind_eq2 acc hA, hv], hyr.trans hr, hym.trans hm⟩

/-- **LDP 64-bit, FEAT_LSE2, 8- but not 16-aligned: `Mem_read__1 a 16 acc true`** = two 8-byte
    single-copy reads, at `a` (low half = bytes 0..7 = first register) then `addInt a 8` (high
    half), each with its own TranslateAddress (size 8). Value = the 16 bytes little-endian;
    registers and memory unchanged; events: TA₁'s, memRead pa₁ 8, TA₂'s, memRead pa₂ 8. -/
theorem pair8_read (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (s : State) (pa1 pa2 : BitVec 56) (data : BitVec (16 * 8))
    (hA : AccDR2 acc) (hP : PostRegs2 s.regs) (hLSE2 : s.regs.FeatureImpl[111] = true)
    (hE1 : TAS a acc pa1 s) (hE2 : TAS (BitVec.addInt a ((8 : Nat) : Int)) acc pa2 s)
    (hio1 : NotMMIO pa1) (hio2 : NotMMIO pa2)
    (hm1 : ∀ i < 8, s.mem[pa1.toNat + i]? = some (data.extractLsb' (8 * i) 8))
    (hm2 : ∀ i < 8, s.mem[pa2.toNat + i]? = some (data.extractLsb' (8 * (i + 8)) 8)) :
    ∃ u1 ad1 t11 x u2 ad2 t21 t,
      Frame s u1 ∧ AArch64_TranslateAddress a acc true ((8 : Nat) : Int) u1 = .ok ad1 t11 ∧
      x.events = t11.events.push (.memRead pa1.toNat 8 (some a.toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      x.regs = s.regs ∧ x.mem = s.mem ∧
      Frame x u2 ∧
      AArch64_TranslateAddress (BitVec.addInt a ((8 : Nat) : Int)) acc true ((8 : Nat) : Int) u2 = .ok ad2 t21 ∧
      Mem_read__1 a 16 acc true s = .ok data t ∧
      t.events = t21.events.push (.memRead pa2.toNat 8 (some (BitVec.addInt a ((8 : Nat) : Int)).toNat)
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  have hb8 : (BitVec.addInt a ((8 : Nat) : Int)).toNat % 8 = 0 := by
    rw [addInt8]; simp [BitVec.toNat_add]; omega
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((16 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  have e5 := lse2_on s3 (by rw [F3.1]; exact hLSE2)
  have hai := allIn16_false a h8 h16 s3
  rcases occ_normal 1644 s3 with ⟨l3, s4, e6, f4⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l3 s4 with ⟨b2, s5, e7, f5⟩
  rcases occ_normal 1645 s5 with ⟨l4, s6, e8, f6⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l4 s6 with ⟨b3, s7, e9, f7⟩
  have F7 := frame_trans (frame_trans (frame_trans (frame_trans F3 f4) f5) f6) f7
  obtain ⟨rc3, e10⟩ : ∃ b, HaveLRCPC3Ext () s7 = .ok b s7 := ⟨_, rfl⟩
  rcases half_read a h8 acc s s7 pa1 (data.extractLsb' 0 64) hA hP hE1 hio1 F7.1 F7.2.1
      (fun i hi => by rw [lo_byte data i hi]; exact hm1 i hi) with
    ⟨u1, ad1, t11, x, fu1, h1, ex, evx, rx, mx⟩
  rcases half_read _ hb8 acc s x pa2 (data.extractLsb' 64 64) hA hP hE2 hio2 rx mx
      (fun i hi => by rw [hi_byte data i hi]; exact hm2 i hi) with
    ⟨u2, ad2, t21, y, fu2, h2, ey, evy, ry, my⟩
  have ex' : AArch64_MemSingle_read__1 a (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false s7
      = .ok (data.extractLsb' 0 64) x := ex
  have ey' : AArch64_MemSingle_read__1 (BitVec.addInt a ((8 : Nat) : Int))
      (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false x
      = .ok (data.extractLsb' 64 64) y := ey
  have hPy : PostRegs y.regs := ry ▸ hP.post
  rcases MemM1.MemReadDBE.be_false y hPy.el0 hPy.nrw hPy.noRME hPy.vhe hPy.aa64el0 hPy.ns hPy.e2h
    hPy.tge hPy.e0e with ⟨t, e11, f11⟩
  have hhalf : Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) = 8 := by decide
  have hal := MemM1.MemReadD.isAligned8 a h8
  have hsz2 : (((((16 : Nat) == 1 || (16 : Nat) == 2) || (16 : Nat) == 4) || (16 : Nat) == 8) || (16 : Nat) == 16) = true := by
    decide
  have hh8 : (((((8 : Nat) == 1 || (8 : Nat) == 2) || (8 : Nat) == 4) || (8 : Nat) == 8)) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  refine ⟨u1, ad1, t11, x, u2, ad2, t21, t, frame_trans F7 fu1, h1, evx, rx, mx, fu2, h2, ?_, f11.2.2.trans evy,
    f11.1.trans ry, f11.2.1.trans my⟩
  unfold Mem_read__1 Mem_read__2 AArch64_MemSingle_read
  simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
    PreSail.assert, hsz2, hh8, hhalf, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, ex', ey', hA.gpr, e11, hal,
    hai, hga, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, Bool.and_true, Bool.true_and, ↓reduceIte, ite_self,
    Sail.BitVec.castWidth_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp (disch := decide) only [cw_toNat, BitVec.append_eq]
  rw [← join_toNat data, BitVec.toNat_append, BitVec.toNat_append]
  have hw : Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int)) * 8
      = 64 := by decide
  rw [hw]
  rfl

#print axioms allIn16_false
#print axioms addInt8
#print axioms lo_byte
#print axioms hi_byte
#print axioms half_read
#print axioms pair8_read
end MemM1.MemPair8R
