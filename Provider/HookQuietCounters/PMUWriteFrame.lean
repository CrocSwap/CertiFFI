import HookQuietCounters.PMUEventNonRetired
import ArmCert.HookQuiet.V0.TransportE20
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded.PMUWriteFrame
open ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet hookQuiet_of_E20Frame)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED from the selected E20 erasure schema. These are actual primitive
register writes, not replacements for PMU hook execution. GIC is proved
separately from E20. Literal public heads have no frame/run/future-Q premise. -/

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_bank_BitVec_64_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.e20_bank_BitVec_64_set"
  (← IO.getStderr).flush

theorem e20_bank_BitVec_64_set (r : Regs) (key : Bank_BitVec_64) (v : BitVec 64)
    (hk : key = .PMCCNTR_EL0 ∨ key = .PMICNTR_EL0 ∨ key = .PMOVSSET_EL0 ∨ key = .PMOVSCLR_EL0 ∨ key = .BRBTS_EL1) :
    E20Frame r {r with bank_BitVec_64 := r.bank_BitVec_64.set key v} := by
  unfold E20Frame eraseE20
  congr 1
  funext k
  by_cases h : k = key
  · subst k
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [RegMap.set]
  · simp [RegMap.set, h]

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_bank_Int_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.e20_bank_Int_set"
  (← IO.getStderr).flush

theorem e20_bank_Int_set (r : Regs) (key : Bank_Int) (v : Int)
    (hk : key = .__clock_divider ∨ key = .__last_cycle_count) :
    E20Frame r {r with bank_Int := r.bank_Int.set key v} := by
  unfold E20Frame eraseE20
  congr 1
  funext k
  by_cases h : k = key
  · subst k
    rcases hk with rfl | rfl <;> simp [RegMap.set]
  · simp [RegMap.set, h]

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_counter_vector_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.e20_counter_vector_set"
  (← IO.getStderr).flush

theorem e20_counter_vector_set (r : Regs) (v : Vector (BitVec 64) 32) :
    E20Frame r {r with bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32.set .PMEVCNTR_EL0 v} := by
  simp only [E20Frame, eraseE20, RegMap.set_set_same]

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_PMUEventAccumulator_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.e20_PMUEventAccumulator_set"
  (← IO.getStderr).flush

theorem e20_PMUEventAccumulator_set (r : Regs) (v : Vector Int 31) :
    E20Frame r {r with PMUEventAccumulator := v} := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_PMULastThresholdValue_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.e20_PMULastThresholdValue_set"
  (← IO.getStderr).flush

theorem e20_PMULastThresholdValue_set (r : Regs) (v : Vector Bool 31) :
    E20Frame r {r with PMULastThresholdValue := v} := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_post_of_frame"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_post_of_frame"
  (← IO.getStderr).flush

private theorem write_post_of_frame {α : Type} (r : RegisterRef Regs α)
    (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : α)
    (hf : E20Frame s.regs (r.set v s.regs))
    (hg : (r.set v s.regs).bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending) :
    (writeReg r v : SailM Unit) s = .ok () {s with regs := r.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := r.set v s.regs} ∧
    ({s with regs := r.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  exact ⟨rfl, ⟨hf, hg, rfl, rfl, rfl, rfl, rfl, rfl, hookQuiet_of_E20Frame hf q⟩, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMICNTR_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_PMICNTR_EL0"
  (← IO.getStderr).flush

theorem write_PMICNTR_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.PMICNTR_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMICNTR_EL0.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.PMICNTR_EL0.set v s.regs} ∧
    ({s with regs := Register.PMICNTR_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMICNTR_EL0 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .PMICNTR_EL0 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMCCNTR_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_PMCCNTR_EL0"
  (← IO.getStderr).flush

theorem write_PMCCNTR_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.PMCCNTR_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMCCNTR_EL0.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.PMCCNTR_EL0.set v s.regs} ∧
    ({s with regs := Register.PMCCNTR_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMCCNTR_EL0 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .PMCCNTR_EL0 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMOVSSET_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_PMOVSSET_EL0"
  (← IO.getStderr).flush

theorem write_PMOVSSET_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.PMOVSSET_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMOVSSET_EL0.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.PMOVSSET_EL0.set v s.regs} ∧
    ({s with regs := Register.PMOVSSET_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMOVSSET_EL0 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .PMOVSSET_EL0 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMOVSCLR_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_PMOVSCLR_EL0"
  (← IO.getStderr).flush

theorem write_PMOVSCLR_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.PMOVSCLR_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMOVSCLR_EL0.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.PMOVSCLR_EL0.set v s.regs} ∧
    ({s with regs := Register.PMOVSCLR_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMOVSCLR_EL0 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .PMOVSCLR_EL0 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_BRBTS_EL1"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_BRBTS_EL1"
  (← IO.getStderr).flush

theorem write_BRBTS_EL1 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.BRBTS_EL1 v : SailM Unit) s = .ok () {s with regs := Register.BRBTS_EL1.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.BRBTS_EL1.set v s.regs} ∧
    ({s with regs := Register.BRBTS_EL1.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.BRBTS_EL1 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .BRBTS_EL1 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMEVCNTR_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_PMEVCNTR_EL0"
  (← IO.getStderr).flush

theorem write_PMEVCNTR_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Vector (BitVec 64) 32) :
    (writeReg Register.PMEVCNTR_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMEVCNTR_EL0.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.PMEVCNTR_EL0.set v s.regs} ∧
    ({s with regs := Register.PMEVCNTR_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMEVCNTR_EL0 budget s q v
  · exact e20_counter_vector_set s.regs v
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMUEventAccumulator"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_PMUEventAccumulator"
  (← IO.getStderr).flush

theorem write_PMUEventAccumulator (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Vector Int 31) :
    (writeReg Register.PMUEventAccumulator v : SailM Unit) s = .ok () {s with regs := Register.PMUEventAccumulator.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.PMUEventAccumulator.set v s.regs} ∧
    ({s with regs := Register.PMUEventAccumulator.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMUEventAccumulator budget s q v
  · exact e20_PMUEventAccumulator_set s.regs v
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMULastThresholdValue"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write_PMULastThresholdValue"
  (← IO.getStderr).flush

theorem write_PMULastThresholdValue (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Vector Bool 31) :
    (writeReg Register.PMULastThresholdValue v : SailM Unit) s = .ok () {s with regs := Register.PMULastThresholdValue.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.PMULastThresholdValue.set v s.regs} ∧
    ({s with regs := Register.PMULastThresholdValue.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMULastThresholdValue budget s q v
  · exact e20_PMULastThresholdValue_set s.regs v
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write___clock_divider"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write___clock_divider"
  (← IO.getStderr).flush

theorem write___clock_divider (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Int) :
    (writeReg Register.__clock_divider v : SailM Unit) s = .ok () {s with regs := Register.__clock_divider.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.__clock_divider.set v s.regs} ∧
    ({s with regs := Register.__clock_divider.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.__clock_divider budget s q v
  · exact e20_bank_Int_set s.regs .__clock_divider v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write___last_cycle_count"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUWriteFrame.write___last_cycle_count"
  (← IO.getStderr).flush

theorem write___last_cycle_count (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Int) :
    (writeReg Register.__last_cycle_count v : SailM Unit) s = .ok () {s with regs := Register.__last_cycle_count.set v s.regs} ∧
    HookQuietCounters.PMUPost budget s {s with regs := Register.__last_cycle_count.set v s.regs} ∧
    ({s with regs := Register.__last_cycle_count.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.__last_cycle_count budget s q v
  · exact e20_bank_Int_set s.regs .__last_cycle_count v (by decide)
  · rfl

#print axioms e20_bank_BitVec_64_set
#print axioms e20_bank_Int_set
#print axioms e20_counter_vector_set
#print axioms e20_PMUEventAccumulator_set
#print axioms e20_PMULastThresholdValue_set
#print axioms write_post_of_frame
#print axioms write_PMICNTR_EL0
#print axioms write_PMCCNTR_EL0
#print axioms write_PMOVSSET_EL0
#print axioms write_PMOVSCLR_EL0
#print axioms write_BRBTS_EL1
#print axioms write_PMEVCNTR_EL0
#print axioms write_PMUEventAccumulator
#print axioms write_PMULastThresholdValue
#print axioms write___clock_divider
#print axioms write___last_cycle_count
end ArmBridge.CruxGenGuarded.PMUWriteFrame
