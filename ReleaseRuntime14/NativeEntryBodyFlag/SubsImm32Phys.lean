import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
import Bridge.RootFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
namespace NativeEntryBodyFlag.SubsImm32Phys

/- GENERATED one-field P-root: ONLY PhysicalCount of the actual successor
(the canonical crux tuple omits it and bkHeap masks it). -/
drive_spec phys_native, phys_complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rn : BitVec 5) (imm12 : BitVec 12)
      (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1 : SailM Unit)
         let u ← get
         pure (u.regs.PhysicalCount, u.mem, u.events)) : SailM _) s

theorem phys (s : ArmBridge.Draft.NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRn : ¬ (Rn.toNat : Int) = 31) :
    (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1 : SailM Unit) s = .ok () (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1 : SailM Unit) s)) ∧
      ((ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1 : SailM Unit) s)).regs.PhysicalCount,
        (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1 : SailM Unit) s)).mem,
        (ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1 : SailM Unit) s)).events) =
        (s.regs.PhysicalCount, s.mem, s.events) := by
  obtain ⟨u, hu⟩ : ∃ u, phys_native s Rn imm12 = .ok (s.regs.PhysicalCount, s.mem, s.events) u := by
    unfold phys_native
    simp (config := {decide := true}) only [hRn, ite_true, ite_false, dite_eq_ite, ite_self]
    exact ⟨_, rfl⟩
  exact ArmBridge.RootFrame.frame_of_root _ (fun u => (u.regs.PhysicalCount, u.mem, u.events)) s u ((phys_complete s Rn imm12 rn el a64 aa64 btype btn).trans hu)

#print axioms phys
end NativeEntryBodyFlag.SubsImm32Phys
