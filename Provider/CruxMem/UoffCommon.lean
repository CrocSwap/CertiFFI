import MemM1.M1Core
import Bridge.CruxGen
import CruxMem.LdstUoffDecode
import CryptoMem.MemCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmCertMem.UoffCommon
open ArmBridge.Draft

/-! Shared helpers for the unsigned-offset single-access crux instances. -/

/-- An Acc0 access descriptor (same fields as memory's J3cV3.accD), used to instantiate permitted premises. -/
def accU : AccessDescriptor :=
  { (default : AccessDescriptor) with
    ss := SecurityState.SS_NonSecure, el := 0#2, acctype := AccessType.AccessType_GPR, tagaccess := false,
    ls64 := false, transactional := false, nonfault := false, firstfault := false }
theorem accU_acc0 : MemM1.Witness.Acc0 accU := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `n` bytes at `pa` hold the little-endian value `d`. -/
def BytesN (mem : Std.ExtHashMap Nat (BitVec 8)) (pa n : Nat) (d : BitVec (n * 8)) : Prop :=
  ∀ i < n, mem[pa + i]? = some (d.extractLsb' (8 * i) 8)

theorem bytesN_unique {mem : Std.ExtHashMap Nat (BitVec 8)} {pa n : Nat} {d1 d2 : BitVec (n * 8)}
    (h1 : BytesN mem pa n d1) (h2 : BytesN mem pa n d2) : d1 = d2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hi : j / 8 < n := by omega
  have e := (h1 (j / 8) hi).symm.trans (h2 (j / 8) hi)
  have e2 := congrArg (fun v => BitVec.getLsbD v (j % 8)) (Option.some.inj e)
  have hm : j % 8 < 8 := Nat.mod_lt _ (by decide)
  have hj' : 8 * (j / 8) + j % 8 = j := Nat.div_add_mod j 8
  simp only [BitVec.getLsbD_extractLsb', hm, decide_true, Bool.true_and, hj'] at e2
  exact e2

/-- No unsigned-offset LDR/STR word is ERET (bit 29 is 1 in the word, 0 in ERET). -/
theorem eret_uoff (size opc : BitVec 2) (imm12 : BitVec 12) (Rn Rt : BitVec 5) :
    (Sail.BitVec.extractLsb (ArmCertMem.LdstUoff.ldstUoffWord size opc imm12 Rn Rt) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg (fun v => BitVec.getLsbD v 17) h
  unfold ArmCertMem.LdstUoff.ldstUoffWord at this
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
  simp only [BitVec.getLsbD_append] at this
  simp at this

/-- X_read of a 32-bit W register (crypto Strb.xread8's proof, width 32). -/
theorem xread32 (s : NativeState) (R : BitVec 5) (hR : R.toNat < 31) :
    X_read ((R.toNat : Nat) : Int) 32 s =
      .ok (BitVec.castWidth (Sail.BitVec.extractLsb (s.regs.gpr[(GPRSummary.key R.toNat).val]) 31 0)) s := by
  unfold X_read get_R
  have htn : Sail.Int.toNatChecked ((R.toNat : Nat) : Int) = R.toNat := rfl
  have h1 : ((R.toNat : Int) ≤ 31) := by omega
  have h2 : ¬ ((R.toNat : Int) = 31) := by omega
  simp [PreSail.assert, bind, EStateM.bind, pure, EStateM.pure, GPRSummary.read_complete, htn, h1, h2,
    CryptoMem.MemCore.cw_extract63]
  rfl

#print axioms xread32
#print axioms bytesN_unique
#print axioms eret_uoff
end ArmCertMem.UoffCommon
