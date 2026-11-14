import MemM1.MemWriteD2
import MemM1.ConsumerD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemWriteD3
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemWriteD1 MemM1.MemWriteD2
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2

theorem constraint_normal (l : ChoiceLabel) : Normal (undefined_Constraint l ()) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

/-- The (pre-translation) endianness test of `Mem_set__2` reads little-endian on every state
    framed from `s` (at EL0 AArch64 this is SCTLR_ELx.E0E = 0 of the EL0 regime; named premise). -/
def LittleEndian (acc : AccessDescriptor) (s : State) : Prop :=
  ∀ u, Frame s u → ∃ u', BigEndian acc.acctype u = .ok false u' ∧ Frame u u'

/-- **Mem_set skeleton.** The actual `Mem_set a n acc v` (the call STRB / STR / the non-LSE2 STP
    halves make: `Mem_set__2 .. ispair=false highestAddressfirst=false`) for an AccDW access at an
    `n`-aligned `a`, `n ∈ {1,2,4,8,16}`, either value of FEAT_LSE2: one MemSingle_set__1 call.
    Relative to the TranslateAddress it runs (state `t1`): exactly one appended `memWrite`, the
    `n` bytes written little-endian at `pa`, registers those of `t1`. -/
theorem memset_skel (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (n * 8)) (hA : AccDW acc)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ Q ad t1)
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
  rcases set_skel a n hn ha acc s5 pa v hA Q (fun u fu => hTA u (frame_trans F5 fu)) hio with
    ⟨ad, t1, t, hQ, hset, hev, hreg, hmem⟩
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

#print axioms constraint_normal
#print axioms memset_skel
end MemM1.MemWriteD3
