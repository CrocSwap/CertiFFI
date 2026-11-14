import Walk.S1EL10PermsCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmFull.Register
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1AIEGuard
abbrev State := S1Normality.State

theorem feature_tcr2 (s : State) :
    HaveFeatTCR2 () s = .ok s.regs.FeatureImpl[178] s := rfl

theorem feature_aie (s : State) :
    HaveAIEExt () s = .ok s.regs.FeatureImpl[181] s := rfl

theorem absent_el1 (s : State) (h : s.regs.FeatureImpl[178] = false) :
    IsTCR2EL1Enabled () s = .ok false s := by
  simp [IsTCR2EL1Enabled, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, feature_tcr2, h]

theorem absent_el2 (s : State) (h : s.regs.FeatureImpl[178] = false) :
    IsTCR2EL2Enabled () s = .ok false s := by
  simp [IsTCR2EL2Enabled, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, feature_tcr2, h]

/- These are the exact AIE-selection subprograms in actual EL10/EL20 parameter
   construction (M0216:656-670 and M0188:337-351). Linking them to the complete
   GetS1TTWParams output remains a separate obligation. -/
def el1 : SailM (BitVec 1) := do
  let enabled ← if (← HaveAIEExt ()) then IsTCR2EL1Enabled () else pure false
  if enabled then
    let raw ← readReg TCR2_EL1
    pure (_get_TCR2_EL1_Type_AIE raw)
  else pure 0#1

def el2 : SailM (BitVec 1) := do
  let enabled ← if (← HaveAIEExt ()) then IsTCR2EL2Enabled () else pure false
  if enabled then
    let raw ← readReg TCR2_EL2
    pure (_get_TCR2_EL2_Type_AIE raw)
  else pure 0#1

theorem absent_aie1 (s : State) (h : s.regs.FeatureImpl[178] = false) :
    el1 s = .ok 0#1 s := by
  cases ha : s.regs.FeatureImpl[181] <;>
    simp [el1, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, feature_aie, ha, absent_el1 s h]

theorem absent_aie2 (s : State) (h : s.regs.FeatureImpl[178] = false) :
    el2 s = .ok 0#1 s := by
  cases ha : s.regs.FeatureImpl[181] <;>
    simp [el2, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, feature_aie, ha, absent_el2 s h]
#print axioms absent_aie1
#print axioms absent_aie2
end S1AIEGuard
