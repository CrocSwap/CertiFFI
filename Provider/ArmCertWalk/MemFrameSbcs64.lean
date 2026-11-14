import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
import Bridge.RootFrame
import Bridge.CruxIAdcs111
import Sail.AbstractRealRat
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
namespace MemFrame.Sbcs64

/- Memory-owned one-field P-root for Sbcs64 (HeapV2 rows: Rm = XZR): ONLY
PhysicalCount of the actual successor. mem/events and ok-ness come from the SDK-canonical
ArmBridge.CruxIAdcs111.madd_frame via CruxIAdcs111.leaf_eq (sbcs 1/1/1 = adcs 1/1/1). -/
drive_spec phys_native, phys_complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd : BitVec 5) (Rn : BitVec 5)
      (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit)
         let u ← get
         pure u.regs.PhysicalCount) : SailM _) s

theorem physCount (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, phys_native s Rd Rn = .ok s.regs.PhysicalCount u := by
  unfold phys_native
  simp (config := {decide := true}) only [hRd, hRn, ite_true, ite_false, dite_eq_ite, ite_self]
  exact ⟨_, rfl⟩

#print axioms physCount

/-- **Sbcs64 (PhysicalCount, mem, events) frame**, NativeEntryBodyFlag.<C>Phys.phys shape. -/
theorem phys (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s = .ok () (ArmBridge.CruxCore.resSt s ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s)) ∧
      ((ArmBridge.CruxCore.resSt s ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s)).regs.PhysicalCount, (ArmBridge.CruxCore.resSt s ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s)).mem, (ArmBridge.CruxCore.resSt s ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s)).events) = (s.regs.PhysicalCount, s.mem, s.events) := by
  obtain ⟨u, hu⟩ := physCount s Rd Rn rd rn el a64 aa64 btype btn hRd hRn
  have count := ArmBridge.RootFrame.frame_of_root _ (fun u => u.regs.PhysicalCount) s u
    ((phys_complete s Rd Rn rd rn el a64 aa64 btype btn).trans hu)
  have frame := ArmBridge.CruxIAdcs111.madd_frame Rat Rd Rn 31#5 s
  rw [← ArmBridge.CruxIAdcs111.leaf_eq] at frame
  unfold ArmBridge.CruxIAdcs111.maddF at frame
  have mem := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) frame.2
  have events := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.1) frame.2
  refine ⟨frame.1, ?_⟩
  simp only at mem events
  rw [count.2, mem, events]

#print axioms phys

end MemFrame.Sbcs64
