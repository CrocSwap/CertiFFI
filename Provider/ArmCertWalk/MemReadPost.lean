-- Additive stronger variant of canonical `MemM1.MemReadIF.read_skel` (proof pinned from it).
-- Difference: no `t1.mem = s.mem`; the four Some bytes and NotMMIO are on the SAME
-- post-translation memory `t1.mem` and the actual returned PA, with existential word.
import MemM1.MemReadIF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedVariables false
namespace ArmCertWalk
open S1Normality MemM1.NoFault MemM1.WitnessIF MemM1.WitnessIFE MemM1.MemReadIF

/-- Actual `AArch64_MemSingle_read pc 4 acc true` for an IFETCH-shaped access at a
4-aligned `pc`. The callback is internal composition only: it is discharged from
actual current data at every framed prefix state. The read value is the actual
current word on the post-translation memory (the walk may have written it). -/
theorem mem_single_read_post (pc : BitVec 64) (hpc : pc.toNat % 4 = 0)
    (acc : AccessDescriptor) (s : MemM1.MemReadIF.State) (hA : AccIFR acc)
    (Q : AddressDescriptor → MemM1.MemReadIF.State → BitVec 32 → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1 data,
      AArch64_TranslateAddress pc acc true ((4 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.vaddress = pc ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧
      NotMMIO ad.paddress.address ∧
      (∀ i < 4, t1.mem[ad.paddress.address.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
      Q ad t1 data) :
    ∃ ad t1 data t, Q ad t1 data ∧ AArch64_MemSingle_read pc 4 acc true s = .ok data t ∧
      t.events = t1.events.push
        (.memRead ad.paddress.address.toNat 4 (some pc.toNat) (AK_ifetch ()) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1631 s with ⟨l1, s1, e1, f1⟩
  rcases bits_normal (Sail.Int.toNatChecked (((4 : Nat) : Int) * 8)) l1 s1 with ⟨b1, s2, e2, f2⟩
  have F2 := frame_trans f1 f2
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s2 = .ok b s2 := ⟨_, rfl⟩
  rcases MemM1.S1T.mte2_normal s2 with ⟨m1, s3, e4, f4⟩
  have F3 := frame_trans F2 f4
  rcases hTA s3 F3 with ⟨ad, t1, data, e5, hf, hva, hspe, hio, hmem, hQ⟩
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
    rw [G7.2.1]; exact hmem
  have e12 := physRead ad acc t7 data hio hm7
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned4 pc hpc
  have hai := allIn16 pc hpc s2
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hsz : ((4 : Nat) == 1 || ((4 : Nat) == 2 || ((4 : Nat) == 4 || ((4 : Nat) == 8 || (4 : Nat) == 16)))) = true := by
    decide
  refine ⟨ad, t1, data, { t7 with events := t7.events.push (.memRead ad.paddress.address.toNat 4
    (some ad.vaddress.toNat) (AccessDescriptor_to_Access_kind acc) false) }, hQ, ?_, ?_, G7.1, G7.2.1⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hva]
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

#print axioms mem_single_read_post
end ArmCertWalk
