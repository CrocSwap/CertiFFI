import GetGuestFields.Dispatch
import Walk.InitTLBSetup
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
set_option maxRecDepth 1000000
namespace GuestSetup
abbrev State := S1Normality.State
def mairBase : BitVec 64 := 0x000000040044ffff#64

/- Finite actual Sail register writes. The unimplemented TCR2 branch is untouched. -/
noncomputable def install (tcr tcr2 : BitVec 64) : SailM Unit := do
  let features ← readReg ArmFull.Register.FeatureImpl
  writeReg (Regs.ref_BitVec_64 .TCR_EL1) tcr
  if features[178] then writeReg (Regs.ref_BitVec_64 .TCR2_EL1) tcr2 else pure ()
  writeReg (Regs.ref_BitVec_64 .MAIR_EL1) mairBase

noncomputable def after (tcr tcr2 : BitVec 64) (s : State) : State :=
  let r1 := (Regs.ref_BitVec_64 .TCR_EL1).set tcr s.regs
  let r2 := if s.regs.FeatureImpl[178] then (Regs.ref_BitVec_64 .TCR2_EL1).set tcr2 r1 else r1
  {s with regs := (Regs.ref_BitVec_64 .MAIR_EL1).set mairBase r2}

theorem install_run (tcr tcr2 : BitVec 64) (s : State) :
    install tcr tcr2 s = .ok () (after tcr tcr2 s) := by
  by_cases h : s.regs.FeatureImpl[178] = true <;>
    simp [install, after, h, readReg, writeReg, PreSail.readReg_apply,
      PreSail.writeReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem after_features (tcr tcr2 : BitVec 64) (s : State) :
    (after tcr tcr2 s).regs.FeatureImpl = s.regs.FeatureImpl := by
  unfold after
  split <;> rfl

theorem after_tcr (tcr tcr2 : BitVec 64) (s : State) :
    (after tcr tcr2 s).regs.bank_BitVec_64 .TCR_EL1 = tcr := by
  by_cases h : s.regs.FeatureImpl[178] = true <;>
    simp [after, h, Regs.ref_BitVec_64, RegMap.set]

theorem after_tcr2 (tcr tcr2 : BitVec 64) (s : State) :
    (after tcr tcr2 s).regs.bank_BitVec_64 .TCR2_EL1 =
      if s.regs.FeatureImpl[178] then tcr2 else s.regs.bank_BitVec_64 .TCR2_EL1 := by
  by_cases h : s.regs.FeatureImpl[178] = true <;>
    simp [after, h, Regs.ref_BitVec_64, RegMap.set]

theorem after_mair (tcr tcr2 : BitVec 64) (s : State) :
    (after tcr tcr2 s).regs.bank_BitVec_64 .MAIR_EL1 = mairBase := by
  by_cases h : s.regs.FeatureImpl[178] = true <;>
    simp [after, h, Regs.ref_BitVec_64, RegMap.set]

theorem after_tlb (tcr tcr2 : BitVec 64) (s : State) :
    (after tcr tcr2 s).regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled := by
  unfold after
  split <;> rfl

theorem after_frame (tcr tcr2 : BitVec 64) (s : State) :
    (after tcr tcr2 s).mem = s.mem ∧ (after tcr tcr2 s).events = s.events ∧
      (after tcr tcr2 s).choiceState = s.choiceState ∧
      (after tcr tcr2 s).choiceOcc = s.choiceOcc := by
  unfold after
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

structure Guards (tcr tcr2 : BitVec 64) : Prop where
  ds : _get_TCR_EL1_Type_DS tcr = 0#1
  d128 : _get_TCR2_EL1_Type_D128 tcr2 = 0#1
  aie : _get_TCR2_EL1_Type_AIE tcr2 = 0#1
  pnch : _get_TCR2_EL1_Type_PnCH tcr2 = 0#1

theorem raw (tcr tcr2 : BitVec 64) (s : State) (h : Guards tcr tcr2) :
    GetGuestFields.Shape.Raw tcr ((after tcr tcr2 s).regs.bank_BitVec_64 .TCR2_EL1)
      (after tcr tcr2 s) := by
  refine ⟨after_tcr tcr tcr2 s, rfl, after_mair tcr tcr2 s, ?_, ?_, ?_, h.ds⟩
  all_goals intro hf
  all_goals have hfs : s.regs.FeatureImpl[178] = true := by simpa only [after_features] using hf
  all_goals rw [after_tcr2, if_pos hfs]
  · exact h.d128
  · exact h.aie
  · exact h.pnch
#print axioms install_run
#print axioms raw
#print axioms after_frame
end GuestSetup
