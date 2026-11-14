import Bridge.CruxGen
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED from the selected native SysEq2 field schema. E20 is required
only for this actual PMU successor. Its actual execution, memory frame and
Q proof must come from the fixed native-owner theorem in the complete bridge.
The old crux_gen/crux_gen_nb theorems are not used. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.spec_input_cong"
  (← IO.getStderr).flush

theorem spec_input_cong (s t : NativeState)
    (hE20 : E20Frame (clrGP (fetchRegs (preFetchRegs s.regs))) t.regs)
    (hm : t.mem = s.mem) (hEL : s.regs.PSTATE.EL = 0#2) : CongIn s t := by
  constructor
  · exact hm.symm
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.gpr)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.SP_EL0)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
  ·
    have hf := frame_pres_E20 (fun x : Regs => x._Z)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
  · constructor
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.FeatureImpl)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.EL)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.nRW)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .SCTLR_EL2)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .TCR_EL2)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .TCR2_EL2)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .HCR_EL2)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .SCR_EL3)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .MAIR_EL2)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .MDSCR_EL1)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .HTTBR)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_128 ._TTBR0_EL2)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_128 .TTBR1_EL2)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => _get_EDSCR_Type_HDE (x.bank_BitVec_32 ._EDSCR))
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_Bool .__tlb_enabled)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_Bool .SPESampleInFlight)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
    ·
      have hf := frame_pres_E20 (fun x : Regs => x.bank_Int .__supported_pa_size)
        (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
      simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.SP_EL1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.SP_EL2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.SP_EL3)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := decide) only [clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne, RegMap.set_same, hde_pipeadv] using hf.symm
  · exact hEL

#print axioms spec_input_cong
end ArmBridge.CruxGenGuarded
