import MemM1.MemReadD2
import MemM1.MemDataV5
import Bridge.StepM
import Bridge.Awc
import Pilot.GPRSummary
import Pilot.Driver
import Pilot.ObservationSimp
import Walk.S1AccDescFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
namespace CryptoMem.MemCore
open ArmBridge.Draft

/-- The native state after writing general register `i`. -/
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

theorem xset (s : NativeState) (R : BitVec 5) (hR : R.toNat < 31) (w : Nat) (hw : w = 32 ∨ w = 64) (v : BitVec w) :
    X_set ((R.toNat : Nat) : Int) w v s =
      .ok () (setGpr s (GPRSummary.key R.toNat) (Sail.BitVec.zeroExtend v 64)) := by
  unfold X_set set_R setGpr
  have htn : Sail.Int.toNatChecked ((R.toNat : Nat) : Int) = R.toNat := rfl
  simp [PreSail.assert, bind, EStateM.bind, pure, EStateM.pure, GPRSummary.write_complete, htn]
  have h1 : ((R.toNat : Int) ≤ 31) := by omega
  have h2 : ¬ ((R.toNat : Int) = 31) := by omega
  rcases hw with rfl | rfl <;> simp [h1, h2, GPRSummary.write_complete, EStateM.pure]

abbrev State := SequentialState Regs oracleChoiceSource


/-- The state formStep runs the decode root on: `__BranchTaken := false`. -/
def brReset (s : NativeState) : NativeState := { s with regs := { s.regs with __BranchTaken := false } }

theorem agrees_congr {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {walk : BitVec 64 → List Nat}
    {s t : NativeState} (h : MemM1.MemDataV3.AgreesV3 m walk s) (hr : t.regs = s.regs) (hm : t.mem = s.mem) :
    MemM1.MemDataV3.AgreesV3 m walk t :=
  fun u hu hmu => h u (hu.trans hr) (hmu.trans hm)

theorem dp_congr {s t : NativeState} (h : ArmCert.Premises.TranslationAgreesV3.DataPins s) (hr : t.regs = s.regs) :
    ArmCert.Premises.TranslationAgreesV3.DataPins t := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨by rw [hr]; exact a, by rw [hr]; exact b, by rw [hr]; exact c, by rw [hr]; exact d, by rw [hr]; exact e⟩

#print axioms agrees_congr
#print axioms dp_congr
#print axioms xread64
#print axioms xset
end CryptoMem.MemCore
