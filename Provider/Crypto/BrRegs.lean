import Pilot.GPRSummary
import Pilot.EvalProfile
import Bridge.Awc
import Bridge.StepM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace Crypto.BrRegs
open ArmBridge.Draft

/-- The native state after writing general register `i` (as CryptoMem.MemCore.setGpr). -/
def setGpr (s : NativeState) (i : Fin 31) (v : BitVec 64) : NativeState :=
  { s with regs := { s.regs with gpr := s.regs.gpr.set i.val v i.isLt } }

theorem cw_extract64 (x : BitVec 64) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((64 : Nat) : Int) - 1)) 0) : BitVec 64) = x := by
  have hw : Sail.Int.toNatChecked (((64 : Nat) : Int) - 1) - 0 + 1 = 64 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [ArmBridge.Awc.castWidth_of_eq hw]
  have hc : Sail.Int.toNatChecked (((64 : Nat) : Int) - 1) = 63 := rfl
  simp [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb, hc, hi]

theorem cw_extract63 (x : BitVec 64) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked 63) 0) : BitVec 64) = x :=
  cw_extract64 x

theorem xread64 (s : NativeState) (R : BitVec 5) (hR : R.toNat < 31) :
    X_read ((R.toNat : Nat) : Int) 64 s = .ok (s.regs.gpr[(GPRSummary.key R.toNat).val]) s := by
  unfold X_read get_R
  have htn : Sail.Int.toNatChecked ((R.toNat : Nat) : Int) = R.toNat := rfl
  have h1 : ((R.toNat : Int) ≤ 31) := by omega
  have h2 : ¬ ((R.toNat : Int) = 31) := by omega
  simp [PreSail.assert, bind, EStateM.bind, pure, EStateM.pure, GPRSummary.read_complete, htn, h1, h2, cw_extract63]

theorem xset30 (s : NativeState) (v : BitVec 64) :
    X_set (30 : Int) 64 v s = .ok () (setGpr s (GPRSummary.key 30) (Sail.BitVec.zeroExtend v 64)) := by
  unfold X_set set_R setGpr
  have htn : Sail.Int.toNatChecked (30 : Int) = 30 := rfl
  simp [PreSail.assert, bind, EStateM.bind, pure, EStateM.pure, GPRSummary.write_complete, htn]

/-- FEAT_GCS is bit 245 of FeatureImpl. -/
theorem gcs_off (s : NativeState) (h : s.regs.FeatureImpl[245] = false) : HaveGCS () s = .ok false s := by
  have h' : (Register.FeatureImpl.get s.regs)[Sail.Int.toNatChecked (num_of_Feature Feature.FEAT_GCS)]! = false := h
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Sail.Int.toNatChecked (num_of_Feature Feature.FEAT_GCS)]! s = _
  rw [h']

theorem pc_read (s : NativeState) : PC_read () s = .ok s.regs._PC s := rfl

#print axioms xread64
#print axioms xset30
#print axioms gcs_off
end Crypto.BrRegs
