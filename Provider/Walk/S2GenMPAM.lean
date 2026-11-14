import Pilot.Driver
import Walk.S2SecurityEL
import Walk.S2MPAMFields
import Walk.S2MPAMPMG
import Walk.S2MPAMPartid
import Walk.S2MPAMCombine
import Walk.S2MPAMCombinedFrame
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2GenMPAM
attribute [-step_summary] S2MPAMMap.complete S2MPAMFields.partidComplete S2MPAMFields.pmgComplete S2MPAMCombine.complete
abbrev State := SequentialState Regs oracleChoiceSource
drive_spec native0, eq0 : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) => GenMPAMatEL .AccessType_TTW 0#2 s
drive_spec native1, eq1 : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) => GenMPAMatEL .AccessType_TTW 1#2 s
drive_spec native2, eq2 : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) => GenMPAMatEL .AccessType_TTW 2#2 s
drive_spec native3, eq3 : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) => GenMPAMatEL .AccessType_TTW 3#2 s
noncomputable def native (el : BitVec 2) (s : State) : EStateM.Result (Sail.Error exception) State MPAMinfo :=
  if el = 0#2 then native0 s else if el = 1#2 then native1 s else
  if el = 2#2 then native2 s else native3 s

theorem complete (el : BitVec 2) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    GenMPAMatEL .AccessType_TTW el s = native el s := by
  by_cases h0 : el = 0#2
  · subst el
    simpa [native] using eq0 s hNoRME hA64 hEL3A64 hNoEL3A32
  by_cases h1 : el = 1#2
  · subst el
    simpa [native] using eq1 s hNoRME hA64 hEL3A64 hNoEL3A32
  by_cases h2 : el = 2#2
  · subst el
    simpa [native] using eq2 s hNoRME hA64 hEL3A64 hNoEL3A32
  have h3 : el = 3#2 := by
    have hb := el.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  subst el
  simpa [native] using eq3 s hNoRME hA64 hEL3A64 hNoEL3A32
attribute [step_summary] complete
#print axioms complete
end S2GenMPAM
