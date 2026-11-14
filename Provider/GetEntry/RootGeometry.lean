import GetEntry.Geometry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 100000
namespace S1EntryRootGeometry

theorem raw_bound (x : BitVec 47) :
    (Sail.BitVec.updateSubrange (0#56) 47 1 x).toNat < 2^48 := by
  have hx := x.isLt
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    BitVec.and_zero, BitVec.zero_or, BitVec.toNat_shiftLeft, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq]
  omega

theorem align4096 (x : BitVec 56) (hx : x.toNat < 2^48) :
    (Align_bits x 4096).toNat % 4096 = 0 ∧ (Align_bits x 4096).toNat < 2^48 := by
  have hn : ¬ ((x.toNat : Int) < (0 : Int)) := by omega
  simp [Align_bits, Align_int, Slice_int, Sail.BitVec.castWidth,
    Sail.BitVec.toNatInt, Sail.BitVec.length, Sail.Int.toNatChecked, get_slice_int,
    fdiv_int, BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_ofInt,
    Nat.shiftRight_zero, hn, Int.ofNat_eq_natCast, ← Int.natCast_ediv, ← Int.natCast_mul, ← Int.natCast_emod]
  omega

#print axioms raw_bound
#print axioms align4096
theorem root_shape (wp : S1TTWParams) (r : Regs) (regime : Regime) (va : BitVec 64)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    (S1EntryRoot.base wp r regime va).toNat % 4096 = 0 ∧
      (S1EntryRoot.base wp r regime va).toNat < 2^48 := by
  unfold S1EntryRoot.base
  rw [S1EntryCallees.start_zero wp hd htg htx]
  exact align4096 _ (raw_bound _)

theorem root_slot (wp : S1TTWParams) (r : Regs) (regime : Regime) (va : BitVec 64)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    (S1EntryRoot.slot wp r regime va).address.toNat =
      S1LogicalReference.entryAddress ((S1EntryRoot.base wp r regime va).setWidth 48) va 0 9 := by
  have hs := root_shape wp r regime va hd htg htx
  exact S1EntryGeometry.first_address _ va hs.1 hs.2
#print axioms root_shape
#print axioms root_slot
end S1EntryRootGeometry

