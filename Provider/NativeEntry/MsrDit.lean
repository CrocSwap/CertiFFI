import NativeEntry.MsrDitRoot
import Bridge.RootFrame
import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntry.MsrDit
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
def expected (s : NativeState) (Rt : BitVec 5) :=
  ({ s.regs with PSTATE := { s.regs.PSTATE with DIT := BitVec.setWidth 1 (BitVec.join1 [BitVec.access s.regs.gpr[(GPRSummary.key Rt.toNat).val] 24]) } }, s.mem, s.events)
def projection (s : NativeState) := (s.regs, s.mem, s.events)

structure Guard (s : NativeState) (Rt : BitVec 5) : Prop where
  rt : Rt.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2
  dit : s.regs.FeatureImpl[103]! = true
  bti : s.regs.FeatureImpl[123]! = true
  tme : s.regs.FeatureImpl[227]! = false
  pmuLower : 0 ≤ s.regs.bank_Int .NUM_PMU_COUNTERS
  pmuUpper : s.regs.bank_Int .NUM_PMU_COUNTERS ≤ 31
  ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  aa32el2 : s.regs.FeatureImpl[2]! = false
  aa32el3 : s.regs.FeatureImpl[3]! = false
  aa64el2 : s.regs.FeatureImpl[6]! = true
  aa64el3 : s.regs.FeatureImpl[7]! = true
  rme : s.regs.FeatureImpl[232]! = false
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  not_br : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 31 25 ≠ 107#7
  not_bti : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 21 12 ≠ 50#10


theorem effect (s : NativeState) (Rt : BitVec 5) (g : Guard s Rt) :
    ∃ t, (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1 : SailM Unit) s = .ok () t ∧
      projection t = expected s Rt := by
  have hRt : ¬ (Rt.toNat : Int) = 31 := by have := g.rt; omega
  have hNUMlow := g.pmuLower
  have hNUMhi := g.pmuUpper
  obtain ⟨u, hu⟩ : ∃ u, effect_native s Rt = .ok (expected s Rt) u := by
    unfold effect_native expected
    simp only [btn_set_zero _ g.btn, hRt, ite_true, ite_false, dite_eq_ite, ite_self, ArmBridge.RootFrame.sw_join1, g.not_br, g.not_bti, NativeEntry.scr_ns_view, g.ns, Spike91.NativeActLib.read63, true_or, or_true, ite_true]

    repeat' first
      | exact ⟨_, rfl⟩
      | (apply ArmBridge.RootFrame.dite_ok <;> intro)
      | (apply NativeEntry.ite_ok <;> intro)
      | (exfalso; omega)
  have root := (effect_complete s Rt g.rt g.el g.a64 g.aa64 g.btype g.btn g.dit g.bti g.tme g.pmuLower g.pmuUpper g.ns g.aa32el2 g.aa32el3 g.aa64el2 g.aa64el3 g.rme g.e2h g.tge g.not_br g.not_bti).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s Rt) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s Rt) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntry.MsrDit
