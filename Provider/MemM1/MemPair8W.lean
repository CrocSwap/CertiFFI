import MemM1.MemPair8R
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemPair8W
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3
open MemM1.MemWriteD4 MemM1.MemWriteD5 MemM1.MemWriteD6 MemM1.MemWriteD7 MemM1.MemPair8R

/-- One 8-byte single-copy store `MemSingle_set__1 b 8 acc true false w` (the pair-split half) on a
    state `x` with `s`'s registers, under the strong premise at `x`. -/
theorem half_set (b : BitVec 64) (hb : b.toNat % 8 = 0) (acc : AccessDescriptor) (s x : State)
    (pa : BitVec 56) (w : BitVec (8 * 8)) (hA : AccDWT acc) (hP : PreW acc s.regs)
    (hspe : s.regs.bank_Bool .SPESampleInFlight = false) (hE : StrongTA b acc 8 pa x)
    (hxr : x.regs = s.regs) (hio : NotMMIO pa) :
    ∃ u ad t1 y, Frame x u ∧ AArch64_TranslateAddress b acc true ((8 : Nat) : Int) u = .ok ad t1 ∧
      AArch64_MemSingle_set__1 b 8 acc true false w x = .ok () y ∧
      y.events = t1.events.push (.memWrite pa.toNat 8 (some b.toNat) akPlain (some w) none) ∧
      y.regs = s.regs ∧ y.mem = wfold x.mem pa.toNat 8 (fun j => w.extractLsb' (8 * j) 8) := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame x u ∧
    AArch64_TranslateAddress b acc true ((8 : Nat) : Int) u = .ok ad t1 ∧ ad.vaddress = b ∧
    t1.regs = x.regs ∧ t1.mem = x.mem
  have h8 : SizeOK 8 := by unfold SizeOK; omega
  rcases set_skelT b 8 h8 hb acc x pa w hA (by unfold TagOK; rw [hxr]; exact hP.tag) Q
      (fun u fu => by
        rcases hE u fu.1 fu.2.1 with ⟨ad, t1, h, hf, hpa, hmt, hv, hr, hm⟩
        have hr' : t1.regs = s.regs := hr.trans (fu.1.trans hxr)
        exact ⟨ad, t1, h, hf, by rw [hpa], by rw [hr']; exact hspe,
          by unfold TagOK; rw [hr']; exact hP.tag, u, fu, h, hv, hr.trans fu.1, hm.trans fu.2.1⟩) hio with
    ⟨ad, t1, y, ⟨u, fu, h1, hv, hr, hm⟩, hy, hev, hyr, hym⟩
  refine ⟨u, ad, t1, y, fu, h1, hy, ?_, hyr.trans (hr.trans hxr), ?_⟩
  · rw [hev, akT acc hA, hv, Sail.BitVec.castWidth_eq]
  · rw [hym, hm, Sail.BitVec.castWidth_eq]

/-- **STP 64-bit, FEAT_LSE2, 8- but not 16-aligned: `Mem_set__1 a 16 acc true v`** = two 8-byte
    single-copy stores: bytes 0..7 of `v` (first register) at `a`, then bytes 8..15 at
    `addInt a 8`, each with its own TranslateAddress (size 8). The second translation runs on the
    state after the first write, so its premise `hE2` is stated at that memory. -/
theorem pair8_set (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (s : State) (v : BitVec (16 * 8)) (hA : AccDWT acc)
    (pa1 pa2 : BitVec 56) (hP : PreW acc s.regs) (hspe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hLSE2 : s.regs.FeatureImpl[111] = true)
    (hE1 : StrongTA a acc 8 pa1 s)
    (hE2 : ∀ s1 : State, s1.regs = s.regs →
      s1.mem = wfold s.mem pa1.toNat 8 (fun j => v.extractLsb' (8 * j) 8) →
      StrongTA (BitVec.addInt a ((8 : Nat) : Int)) acc 8 pa2 s1)
    (hio1 : NotMMIO pa1) (hio2 : NotMMIO pa2) :
    ∃ u1 ad1 t11 x u2 ad2 t21 t,
      Frame s u1 ∧ AArch64_TranslateAddress a acc true ((8 : Nat) : Int) u1 = .ok ad1 t11 ∧
      x.events = t11.events.push (.memWrite pa1.toNat 8 (some a.toNat) akPlain
        (some (v.extractLsb' 0 64)) none) ∧
      x.regs = s.regs ∧ x.mem = wfold s.mem pa1.toNat 8 (fun j => v.extractLsb' (8 * j) 8) ∧
      Frame x u2 ∧
      AArch64_TranslateAddress (BitVec.addInt a ((8 : Nat) : Int)) acc true ((8 : Nat) : Int) u2 = .ok ad2 t21 ∧
      Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = t21.events.push (.memWrite pa2.toNat 8 (some (BitVec.addInt a ((8 : Nat) : Int)).toNat)
        akPlain (some (v.extractLsb' 64 64)) none) ∧
      t.regs = s.regs ∧
      t.mem = wfold x.mem pa2.toNat 8 (fun j => v.extractLsb' (8 * (j + 8)) 8) := by
  have hb8 : (BitVec.addInt a ((8 : Nat) : Int)).toNat % 8 = 0 := by
    rw [addInt8]; simp [BitVec.toNat_add]; omega
  rcases occ_normal 1646 s with ⟨l1, s1, e1, f1⟩
  rcases constraint_normal l1 s1 with ⟨c, s2, e2, f2⟩
  rcases occ_normal 1647 s2 with ⟨l2, s3, e3, f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp, s4, e4, f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  rcases littleEndian_of acc s hA hP s4 F4 with ⟨s5, e5, f5⟩
  have F5 := frame_trans F4 f5
  have e6 := lse2_on s5 (by rw [F5.1]; exact hLSE2)
  have hai := allIn16_false a h8 h16 s5
  rcases occ_normal 1650 s5 with ⟨l3, s6, e7, f6⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l3 s6 with ⟨b2, s7, e8, f7⟩
  rcases occ_normal 1651 s7 with ⟨l4, s8, e9, f8⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l4 s8 with ⟨b3, s9, e10, f9⟩
  have F9 := frame_trans (frame_trans (frame_trans (frame_trans F5 f6) f7) f8) f9
  obtain ⟨rc3, e11⟩ : ∃ b, HaveLRCPC3Ext () s9 = .ok b s9 := ⟨_, rfl⟩
  rcases half_set a h8 acc s s9 pa1 (v.extractLsb' 0 64) hA hP hspe
      (fun u hu hum => hE1 u (hu.trans F9.1) (hum.trans F9.2.1)) F9.1 hio1 with
    ⟨u1, ad1, t11, x, fu1, h1, ex, evx, rx, mx⟩
  have mx' : x.mem = wfold s.mem pa1.toNat 8 (fun j => v.extractLsb' (8 * j) 8) := by
    rw [mx, F9.2.1]
    unfold wfold
    congr 2
    funext j
    exact Prod.ext rfl (lo_byte v j.val j.isLt)
  rcases half_set _ hb8 acc s x pa2 (v.extractLsb' 64 64) hA hP hspe (hE2 x rx mx') rx hio2 with
    ⟨u2, ad2, t21, t, fu2, h2, ey, evy, ry, my⟩
  have hhalf : Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) = 8 := by decide
  have hal := MemM1.MemReadD.isAligned8 a h8
  have hsimd : (BEq.beq acc.acctype AccessType.AccessType_ASIMD) = false := by
    rw [hA.base.gpr]; rfl
  refine ⟨u1, ad1, t11, x, u2, ad2, t21, t, frame_trans F9 fu1, h1, evx, rx, mx', fu2, h2, ?_, evy, ry, ?_⟩
  rotate_left
  · rw [my]
    unfold wfold
    congr 2
    funext j
    exact Prod.ext rfl (hi_byte v j.val j.isLt)
  have ex' : AArch64_MemSingle_set__1 a (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false
      (v.extractLsb' 0 64) s9 = .ok () x := ex
  have ey' : AArch64_MemSingle_set__1 (BitVec.addInt a ((8 : Nat) : Int))
      (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false
      (v.extractLsb' 64 64) x = .ok () t := ey
  unfold Mem_set__1 Mem_set__2
  simp (config := { decide := true }) only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure,
    EStateM.pure, ArmFull.assert, PreSail.assert, hhalf, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
    hal, hai, hsimd, Sail.BitVec.castWidth_eq, Bool.and_false, Bool.false_and, Bool.or_false,
    Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true, Bool.true_and,
    ↓reduceIte, ite_self]
  erw [ex']
  simp only []
  erw [ey']

#print axioms half_set
#print axioms pair8_set
end MemM1.MemPair8W
