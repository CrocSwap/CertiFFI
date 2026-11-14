import Pilot.UndefSummaries
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1WalkDecode
abbrev State := SequentialState Regs oracleChoiceSource

theorem cases2 (x : BitVec 2) : x = 0#2 ∨ x = 1#2 ∨ x = 2#2 ∨ x = 3#2 := by
  have hx := x.isLt
  have hc : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 := by omega
  rcases hc with h | h | h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h)))

drive_spec share0, share0_eq : fun (s : State) => DecodeShareability 0#2 s
drive_spec share1, share1_eq : fun (s : State) => DecodeShareability 1#2 s
drive_spec share2, share2_eq : fun (s : State) => DecodeShareability 2#2 s
drive_spec share3, share3_eq : fun (s : State) => DecodeShareability 3#2 s

noncomputable def share (x : BitVec 2) : SailM Shareability :=
  if x = 0#2 then share0 else if x = 1#2 then share1 else if x = 2#2 then share2 else share3

theorem share_eq (x : BitVec 2) (s : State) : DecodeShareability x s = share x s := by
  rcases cases2 x with rfl | rfl | rfl | rfl
  · exact share0_eq s
  · exact share1_eq s
  · exact share2_eq s
  · exact share3_eq s
attribute [step_summary] share_eq

drive_spec sdf0, sdf0_eq : fun (s : State) => DecodeSDFAttr 0#2 s
drive_spec sdf1, sdf1_eq : fun (s : State) => DecodeSDFAttr 1#2 s
drive_spec sdf2, sdf2_eq : fun (s : State) => DecodeSDFAttr 2#2 s
drive_spec sdf3, sdf3_eq : fun (s : State) => DecodeSDFAttr 3#2 s

noncomputable def sdf (x : BitVec 2) : SailM MemAttrHints :=
  if x = 0#2 then sdf0 else if x = 1#2 then sdf1 else if x = 2#2 then sdf2 else sdf3

theorem sdf_eq (x : BitVec 2) (s : State) : DecodeSDFAttr x s = sdf x s := by
  rcases cases2 x with rfl | rfl | rfl | rfl
  · exact sdf0_eq s
  · exact sdf1_eq s
  · exact sdf2_eq s
  · exact sdf3_eq s
attribute [step_summary] sdf_eq
#print axioms share_eq
#print axioms sdf_eq
end S1WalkDecode
