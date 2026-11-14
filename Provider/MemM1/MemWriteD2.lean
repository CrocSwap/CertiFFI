import MemM1.MemWriteD1
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemWriteD2
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemWriteD1

/-- The EL0 NS plain GPR data-write access shape: `Witness.Acc0` plus the flags MemSingle_set
    tests (all false in what `CreateAccDescGPR STORE` returns for a plain STR/STP at EL0 with
    TME off or TSTATE.depth = 0 and tagchecked = false). -/
structure AccDW (acc : AccessDescriptor) : Prop where
  base : MemM1.Witness.Acc0 acc
  tagchecked : acc.tagchecked = false
  exclusive : acc.exclusive = false
  atomicop : acc.atomicop = false
  acqsc : acc.acqsc = false
  acqpc : acc.acqpc = false
  relsc : acc.relsc = false

theorem sizeOK_beq (n : Nat) (hn : SizeOK n) :
    ((n == 1) || ((n == 2) || ((n == 4) || ((n == 8) || (n == 16))))) = true := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide

/-- MemSingle_set skeleton: the actual `AArch64_MemSingle_set__1 a n acc true false v` (aligned,
    not a pair) for an `AccDW` access at an `n`-aligned `a`, given what TranslateAddress returns
    on any state framed from `s`. After TranslateAddress (state `t1`) it only draws choice
    bookkeeping and issues ONE `PhysMemWrite`: one `memWrite` event, then the `n` bytes. -/
theorem set_skel (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (n * 8)) (hA : AccDW acc)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ AArch64_MemSingle_set__1 a n acc true false v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat n (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) := by
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s = .ok b s := ⟨_, rfl⟩
  rcases MemM1.S1T.mte2_normal s with ⟨m1, s3, e4, f4⟩
  rcases hTA s3 f4 with ⟨ad, t1, e5, hf, hpa, hspe, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  rcases MemM1.S1T.mte2_normal t2 with ⟨m2, t3, e7, f7⟩
  have G3 := frame_trans f6 f7
  have hspe3 : Register.SPESampleInFlight.get t3.regs = false := by rw [G3.1]; exact hspe
  rcases occ_normal 1636 t3 with ⟨l2, t4, e8, f8⟩
  rcases physstat_normal l2 t4 with ⟨ps, t5, e9, f9⟩
  rcases occ_normal 1637 t5 with ⟨l3, t6, e10, f10⟩
  rcases S1EntryCalleesExtra.bool_normal l3 t6 with ⟨b3, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans G3 f8) f9) f10) f11
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
      PreSail.assert, hsz, hnn, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai, hA.tagchecked,
      hA.exclusive, hA.atomicop, hA.acqsc, hA.acqpc, hA.relsc, hA.base.tx, IsFault, hfn, IsFault__2,
      CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, bne_self_eq_false]
    done

#print axioms set_skel
end MemM1.MemWriteD2
