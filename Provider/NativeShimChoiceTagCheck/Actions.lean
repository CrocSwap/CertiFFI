import NativeTagCheck.Tail
import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
import NativeEntry.BtiC
import NativeEntry.MrsDit
import NativeEntry.DitOn
import NativeEntry.MsrDit
import NativeEntry.IsbSy
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
namespace NativeShimChoiceTagCheck

theorem getD_ite (p : Prop) [Decidable p] (a b : Std.ExtHashMap Nat Nat) (key fallback : Nat) :
    (if p then a else b).getD key fallback =
      if p then a.getD key fallback else b.getD key fallback := by
  split <;> rfl

attribute [local simp] getD_ite Std.ExtHashMap.getD_insert
  NativeEntry.scr_ns_view Spike91.NativeActLib.read63

namespace BtiC
drive_spec choice_native, choice_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      
       =>
    ((do let _ ← (decode_bti_aarch64_instrs_system_hints 2#3 4#4 : SailM Unit)
         let u ← get
         pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s


theorem action_choice (s t : NativeState)
    (run : (decode_bti_aarch64_instrs_system_hints 2#3 4#4 : SailM Unit) s = .ok () t) :
    ChoiceDelta s t 0 := by
  have observed : ((do let _ ← (decode_bti_aarch64_instrs_system_hints 2#3 4#4 : SailM Unit)
                       let u ← get
                       pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s =
      .ok (t.choiceState.1, t.choiceOcc.getD 1354 0) t := by
    rw [ArmBridge.CruxCore.bind_app,run]
    rfl
  rw [choice_complete s] at observed

  obtain ⟨u, output⟩ : ∃ u, choice_native s =
      .ok (s.choiceState.1, s.choiceOcc.getD 1354 0) u := by
    observe_simp [choice_native]
    all_goals simp [Std.ExtHashMap.getD_insert]
  have same := (EStateM.Result.ok.inj (output.symm.trans observed)).1
  exact ⟨(congrArg Prod.fst same).symm, by simpa using (congrArg Prod.snd same).symm⟩


#print axioms choice_complete
#print axioms action_choice
end BtiC

namespace MrsDit
drive_spec choice_native, choice_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      (Rt : BitVec 5)
      (rt : Rt.toNat < 31)
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (btype : s.regs.PSTATE.BTYPE = 0#2)
      (btn : s.regs.BTypeNext = 0#2)
      (dit : s.regs.FeatureImpl[103]! = true)
      (bti : s.regs.FeatureImpl[123]! = true)
      (tme : s.regs.FeatureImpl[227]! = false) =>
    ((do let _ ← (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s


theorem action_choice (s t : NativeState) (Rt : BitVec 5) (g : NativeEntry.MrsDit.Guard s Rt)
    (run : (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1 : SailM Unit) s = .ok () t) :
    ChoiceDelta s t 0 := by
  have observed : ((do let _ ← (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1 : SailM Unit)
                       let u ← get
                       pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s =
      .ok (t.choiceState.1, t.choiceOcc.getD 1354 0) t := by
    rw [ArmBridge.CruxCore.bind_app,run]
    rfl
  rw [choice_complete s Rt g.rt g.el g.a64 g.aa64 g.btype g.btn g.dit g.bti g.tme] at observed

  obtain ⟨u, output⟩ : ∃ u, choice_native s Rt =
      .ok (s.choiceState.1, s.choiceOcc.getD 1354 0) u := by
    observe_simp [choice_native]
    all_goals simp [Std.ExtHashMap.getD_insert]
  have same := (EStateM.Result.ok.inj (output.symm.trans observed)).1
  exact ⟨(congrArg Prod.fst same).symm, by simpa using (congrArg Prod.snd same).symm⟩


#print axioms choice_complete
#print axioms action_choice
end MrsDit

namespace DitOn
drive_spec choice_native, choice_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (btype : s.regs.PSTATE.BTYPE = 0#2)
      (word : s.regs.bank_BitVec_32 .__ThisInstr = 0xd503415f#32)
      (dit : s.regs.FeatureImpl[103]! = true)
      (bti : s.regs.FeatureImpl[123]! = true)
      (tme : s.regs.FeatureImpl[227]! = false) =>
    ((do let _ ← (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3 : SailM Unit)
         let u ← get
         pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s


theorem action_choice (s t : NativeState) (g : NativeEntry.DitOn.Guard s)
    (run : (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3 : SailM Unit) s = .ok () t) :
    ChoiceDelta s t 0 := by
  have observed : ((do let _ ← (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3 : SailM Unit)
                       let u ← get
                       pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s =
      .ok (t.choiceState.1, t.choiceOcc.getD 1354 0) t := by
    rw [ArmBridge.CruxCore.bind_app,run]
    rfl
  rw [choice_complete s g.el g.a64 g.aa64 g.btype g.word g.dit g.bti g.tme] at observed

  obtain ⟨u, output⟩ : ∃ u, choice_native s =
      .ok (s.choiceState.1, s.choiceOcc.getD 1354 0) u := by
    observe_simp [choice_native]
    all_goals simp [Std.ExtHashMap.getD_insert]
  have same := (EStateM.Result.ok.inj (output.symm.trans observed)).1
  exact ⟨(congrArg Prod.fst same).symm, by simpa using (congrArg Prod.snd same).symm⟩


#print axioms choice_complete
#print axioms action_choice
end DitOn

namespace MsrDit
drive_spec choice_native, choice_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      (Rt : BitVec 5)
      (rt : Rt.toNat < 31)
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (btype : s.regs.PSTATE.BTYPE = 0#2)
      (btn : s.regs.BTypeNext = 0#2)
      (dit : s.regs.FeatureImpl[103]! = true)
      (bti : s.regs.FeatureImpl[123]! = true)
      (tme : s.regs.FeatureImpl[227]! = false)
      (pmuLower : 0 ≤ s.regs.bank_Int .NUM_PMU_COUNTERS)
      (pmuUpper : s.regs.bank_Int .NUM_PMU_COUNTERS ≤ 31)
      (ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
      (aa32el2 : s.regs.FeatureImpl[2]! = false)
      (aa32el3 : s.regs.FeatureImpl[3]! = false)
      (aa64el2 : s.regs.FeatureImpl[6]! = true)
      (aa64el3 : s.regs.FeatureImpl[7]! = true)
      (rme : s.regs.FeatureImpl[232]! = false)
      (e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (not_br : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 31 25 ≠ 107#7)
      (not_bti : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 21 12 ≠ 50#10) =>
    ((do let _ ← (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1 : SailM Unit)
         let u ← get
         pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s


theorem action_choice (s t : NativeState) (Rt : BitVec 5) (g : NativeEntry.MsrDit.Guard s Rt)
    (run : (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1 : SailM Unit) s = .ok () t) :
    ChoiceDelta s t 0 := by
  have observed : ((do let _ ← (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1 : SailM Unit)
                       let u ← get
                       pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s =
      .ok (t.choiceState.1, t.choiceOcc.getD 1354 0) t := by
    rw [ArmBridge.CruxCore.bind_app,run]
    rfl
  rw [choice_complete s Rt g.rt g.el g.a64 g.aa64 g.btype g.btn g.dit g.bti g.tme g.pmuLower g.pmuUpper g.ns g.aa32el2 g.aa32el3 g.aa64el2 g.aa64el3 g.rme g.e2h g.tge g.not_br g.not_bti] at observed
  have h_rt := g.rt
  have h_el := g.el
  have h_a64 := g.a64
  have h_aa64 := g.aa64
  have h_btype := g.btype
  have h_btn := g.btn
  have h_dit := g.dit
  have h_bti := g.bti
  have h_tme := g.tme
  have h_pmuLower := g.pmuLower
  have h_pmuUpper := g.pmuUpper
  have h_ns := g.ns
  have h_aa32el2 := g.aa32el2
  have h_aa32el3 := g.aa32el3
  have h_aa64el2 := g.aa64el2
  have h_aa64el3 := g.aa64el3
  have h_rme := g.rme
  have h_e2h := g.e2h
  have h_tge := g.tge
  have h_not_br := g.not_br
  have h_not_bti := g.not_bti

  obtain ⟨u, output⟩ : ∃ u, choice_native s Rt =
      .ok (s.choiceState.1, s.choiceOcc.getD 1354 0) u := by
    observe_simp [choice_native]
    all_goals try simp only [NativeEntry.scr_ns_view, g.ns, Spike91.NativeActLib.read63,
      true_or, or_true, ite_true, Std.ExtHashMap.getD_insert]
    all_goals observe_simp []
    repeat' first
      | (observe_simp []; all_goals exact ⟨_,rfl⟩)
      | (apply ArmBridge.RootFrame.dite_ok <;> intro)
      | (apply NativeEntry.ite_ok <;> intro)
      | (exfalso; omega)
  have same := (EStateM.Result.ok.inj (output.symm.trans observed)).1
  exact ⟨(congrArg Prod.fst same).symm, by simpa using (congrArg Prod.snd same).symm⟩


#print axioms choice_complete
#print axioms action_choice
end MsrDit

namespace IsbSy
set_option maxHeartbeats 800000 in
drive_spec choice_native, choice_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (aa32el2 : s.regs.FeatureImpl[2]! = false)
      (aa32el3 : s.regs.FeatureImpl[3]! = false)
      (aa64el2 : s.regs.FeatureImpl[6]! = true)
      (aa64el3 : s.regs.FeatureImpl[7]! = true)
      (rme : s.regs.FeatureImpl[232]! = false)
      (e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
      (brbe : s.regs.FeatureImpl[230]! = false)
      (spe : s.regs.bank_Bool .SPESampleInFlight = false) =>
    ((do let _ ← (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit)
         let u ← get
         pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s


theorem action_choice (s t : NativeState) (g : NativeEntry.IsbSy.Guard s)
    (run : (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit) s = .ok () t) :
    ChoiceDelta s t 0 := by
  have observed : ((do let _ ← (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit)
                       let u ← get
                       pure (u.choiceState.1, u.choiceOcc.getD 1354 0)) : SailM _) s =
      .ok (t.choiceState.1, t.choiceOcc.getD 1354 0) t := by
    rw [ArmBridge.CruxCore.bind_app,run]
    rfl
  rw [choice_complete s g.el g.a64 g.aa64 g.aa32el2 g.aa32el3 g.aa64el2 g.aa64el3 g.rme g.e2h g.tge g.ns g.brbe g.spe] at observed
  have h_el := g.el
  have h_a64 := g.a64
  have h_aa64 := g.aa64
  have h_aa32el2 := g.aa32el2
  have h_aa32el3 := g.aa32el3
  have h_aa64el2 := g.aa64el2
  have h_aa64el3 := g.aa64el3
  have h_rme := g.rme
  have h_e2h := g.e2h
  have h_tge := g.tge
  have h_ns := g.ns
  have h_brbe := g.brbe
  have h_spe := g.spe

  obtain ⟨u, output⟩ : ∃ u, choice_native s =
      .ok (s.choiceState.1, s.choiceOcc.getD 1354 0) u := by
    observe_simp [choice_native]
    all_goals try simp only [NativeEntry.scr_ns_view, g.ns, Spike91.NativeActLib.read63,
      true_or, or_true, ite_true, Std.ExtHashMap.getD_insert]
    all_goals observe_simp []
    repeat' first
      | (observe_simp []; all_goals exact ⟨_,rfl⟩)
      | (apply ArmBridge.RootFrame.dite_ok <;> intro)
      | (apply NativeEntry.ite_ok <;> intro)
      | (exfalso; omega)
  have same := (EStateM.Result.ok.inj (output.symm.trans observed)).1
  exact ⟨(congrArg Prod.fst same).symm, by simpa using (congrArg Prod.snd same).symm⟩


#print axioms choice_complete
#print axioms action_choice
end IsbSy

end NativeShimChoiceTagCheck
