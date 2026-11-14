import NativeEntryCallerTransport.Pins
import Bridge.CruxGenGuarded.EntryTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open NativeEntryCallerParts NativeEntryCallerTransport
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Actual caller actions preserve SysEq2's 17 fields. This does NOT claim
historical bkHeap NPE: the real SPE path can clear PrevValid. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.caller_controls_after_E20"
  (← IO.getStderr).flush

theorem caller_controls_after_E20 (s t : NativeState) (hp : CallerControls s)
    (frame : E20Frame s.regs t.regs) : CallerControls t := by
  constructor
  · have hf := frame_pres_E20 (fun r : Regs => r.FeatureImpl[4]! = true)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.f4
  · have hf := frame_pres_E20 (fun r : Regs => r.FeatureImpl[2]! = false)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.f2
  · have hf := frame_pres_E20 (fun r : Regs => r.FeatureImpl[3]! = false)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.f3
  · have hf := frame_pres_E20 (fun r : Regs => r.FeatureImpl[6]! = true)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.f6
  · have hf := frame_pres_E20 (fun r : Regs => r.FeatureImpl[7]! = true)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.f7
  · have hf := frame_pres_E20 (fun r : Regs => r.FeatureImpl[232]! = false)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.rme
  · have hf := frame_pres_E20 (fun r : Regs => r.FeatureImpl[54]! = true)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.vhe
  · have hf := frame_pres_E20 (fun r : Regs => r.FeatureImpl[230]! = false)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.brbe
  · have hf := frame_pres_E20 (fun r : Regs => r.PSTATE.EL = 0#2)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.el
  · have hf := frame_pres_E20 (fun r : Regs => r.PSTATE.nRW = 0#1)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.nrw
  · have hf := frame_pres_E20 (fun r : Regs => _get_HCR_EL2_Type_E2H (r.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.e2h
  · have hf := frame_pres_E20 (fun r : Regs => _get_HCR_EL2_Type_TGE (r.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.tge
  · have hf := frame_pres_E20 (fun r : Regs => _get_SCR_EL3_Type_NS (r.bank_BitVec_64 .SCR_EL3) = 1#1)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.ns
  · have hf := frame_pres_E20 (fun r : Regs => _get_PMBLIMITR_EL1_Type_E (r.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.pmb
  · have hf := frame_pres_E20 (fun r : Regs => r.bank_Bool .SPESampleInFlight = false)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.spe
  · have hf := frame_pres_E20 (fun r : Regs => Sail.BitVec.extractLsb (r.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.pmbs
  · have hf := frame_pres_E20 (fun r : Regs => _get_MDCR_EL3_Type_NSPB (r.bank_BitVec_64 .MDCR_EL3) = 3#2)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.nspb
  · have hf := frame_pres_E20 (fun r : Regs => _get_MDCR_EL3_Type_NSPBE (r.bank_BitVec_64 .MDCR_EL3) = 0#1)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.nspbe
  · have hf := frame_pres_E20 (fun r : Regs => _get_SCR_EL3_Type_GCSEn (r.bank_BitVec_64 .SCR_EL3) = 0#1)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) frame
    exact hf.mpr hp.gcsEn

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.caller_controls_at_metadata"
  (← IO.getStderr).flush

theorem caller_controls_at_metadata (s : NativeState) (w : BitVec 32) (K : Int)
    (hp : CallerControls s) : CallerControls (actionState w s K) := by
  constructor
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.f4
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.f2
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.f3
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.f6
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.f7
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.rme
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.vhe
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.brbe
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.el
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.nrw
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.e2h
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.tge
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.ns
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.pmb
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.spe
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.pmbs
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.nspb
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.nspbe
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.gcsEn

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.caller_metadata_sys"
  (← IO.getStderr).flush

theorem caller_metadata_sys (s : NativeState) (w : BitVec 32) (K : Int)
    (hp : NativeEntryTail.EntryPins s) : SysEq2 s.regs (actionState w s K).regs := by
  constructor
  all_goals first
    | rfl
    | simp (disch := decide) only [actionState, RegMap.set_ne, hp.el, hp.nrw]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.caller_metadata_branch"
  (← IO.getStderr).flush

theorem caller_metadata_branch (s : NativeState) (w : BitVec 32) (K : Int) :
    BrSysEq s.regs (actionState w s K).regs := by
  constructor <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.caller_metadata_output"
  (← IO.getStderr).flush

theorem caller_metadata_output (s : NativeState) (w : BitVec 32) (K : Int) :
    CongOut (actionState w s K) s := by
  constructor <;> rfl

#print axioms caller_controls_after_E20
#print axioms caller_controls_at_metadata
#print axioms caller_metadata_sys
#print axioms caller_metadata_branch
#print axioms caller_metadata_output
end ArmBridge.CruxGenGuarded
