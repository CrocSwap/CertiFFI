import GuestSetup.Join
import Walk.S1OuterSetup
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.JointSAT
abbrev State := S1Normality.State

/- a design decision. Label: non-vacuity witness under implementation profile
; not power-on reachability.
   A2: implementation config selected through the model's own __SetConfig API.
   B2: FeatureImpl / PSTATE / __supported_pa_size written directly as a named
   implementation-profile setup step. -/

theorem set_rme (s : State) :
    __SetConfig "cpu.has_rme" 0 s =
      .ok () {s with regs := (Regs.ref_Bool .FEAT_RME_IMPLEMENTED).set false s.regs} := by
  rfl

theorem set_pa (s : State) :
    __SetConfig "cpu.PA_SIZE" 48 s =
      .ok () {s with regs := (Regs.ref_Int .__supported_pa_size).set 48 s.regs} := by
  rfl

/-- Named feature-vector inputs of the implementation profile. -/
structure FeatureGuards (fv : Vector Bool 259) : Prop where
  noRME : fv[232] = false
  el3A64 : fv[7] = true
  noEL3A32 : fv[3] = false
  aa64EL0 : fv[4] = true
  aa64EL1 : fv[5] = true
  aa64EL2 : fv[6] = true
  /-- FEAT_VHE (54): GB10 runs a VHE host; needed for TranslationRegime(EL0) = EL2&0. -/
  vhe : fv[54] = true

noncomputable def implProfile (fv : Vector Bool 259) : SailM Unit := do
  __SetConfig "cpu.has_rme" 0
  __SetConfig "cpu.PA_SIZE" 48
  writeReg ArmFull.Register.FeatureImpl fv
  let p ← readReg ArmFull.Register.PSTATE
  writeReg ArmFull.Register.PSTATE {p with EL := 1#2, nRW := 0#1}
  writeReg (Regs.ref_Int .__supported_pa_size) 48

def implRegs (fv : Vector Bool 259) (r : Regs) : Regs :=
  let r1 := (Regs.ref_Bool .FEAT_RME_IMPLEMENTED).set false r
  let r2 := (Regs.ref_Int .__supported_pa_size).set 48 r1
  let r3 := ArmFull.Register.FeatureImpl.set fv r2
  let r4 := ArmFull.Register.PSTATE.set {r3.PSTATE with EL := 1#2, nRW := 0#1} r3
  (Regs.ref_Int .__supported_pa_size).set 48 r4

theorem impl_run (fv : Vector Bool 259) (s : State) :
    implProfile fv s = .ok () {s with regs := implRegs fv s.regs} := by
  rfl

/- Architectural setup: HCR_EL2 for EL1&0 stage-1 only (VM = DC = 0). -/
def hcr : BitVec 64 := 0#64

noncomputable def archHCR : SailM Unit := writeReg (Regs.ref_BitVec_64 .HCR_EL2) hcr

theorem hcr_run (s : State) :
    archHCR s = .ok () {s with regs := (Regs.ref_BitVec_64 .HCR_EL2).set hcr s.regs} := by
  rfl

theorem hcr_vm : _get_HCR_EL2_Type_VM hcr = 0#1 := by decide
theorem hcr_dc : _get_HCR_EL2_Type_DC hcr = 0#1 := by decide

#print axioms set_rme
#print axioms set_pa
#print axioms impl_run
#print axioms hcr_run
end ArmCert.Eval.JointSAT
