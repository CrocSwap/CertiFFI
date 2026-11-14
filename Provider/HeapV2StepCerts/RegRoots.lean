-- Memory (certiffi (c2), approved 4de3): one-field (gpr, SP_EL0) roots of the actual successor for
-- Csel3 / Csinc3 (no b1/b2 value lemma exists; Sbcs64 is in Sbcs64Body): the class writes only X[Rd] and leaves SP.
-- drive_spec at a per-declaration 400k heartbeat budget (, AGENTS.md per-decl rule).
import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
import Bridge.RootFrame
import Bridge.CruxCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1000000
namespace HeapV2StepCerts.RegRoots

namespace Csel3
set_option maxHeartbeats 400000 in
drive_spec regs_native, regs_complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd : BitVec 5) (Rn : BitVec 5)
      (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (spe : s.regs.bank_Bool .SPESampleInFlight = false) =>
    ((do let _ ← (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0)) : SailM _) s

theorem regs (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (spe : s.regs.bank_Bool .SPESampleInFlight = false) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s =
      .ok () (ArmBridge.CruxCore.resSt s ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s)) ∧
    ∃ v : BitVec 64, (ArmBridge.CruxCore.resSt s ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s)).regs.gpr =
        s.regs.gpr.set (GPRSummary.key Rd.toNat).val v (GPRSummary.key Rd.toNat).isLt ∧
      (ArmBridge.CruxCore.resSt s ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s)).regs.SP_EL0 = s.regs.SP_EL0 := by
  have key : ∃ (v : BitVec 64) (u : ArmBridge.Draft.NativeState), regs_native s Rd Rn =
      .ok (s.regs.gpr.set (GPRSummary.key Rd.toNat).val v (GPRSummary.key Rd.toNat).isLt, s.regs.SP_EL0) u := by
    unfold regs_native
    simp only [hRd, hRn, spe, ite_true, ite_false, dite_eq_ite, ite_self]
    by_cases hc : s.regs.PSTATE.C = 1#1 <;> simp only [hc, ↓reduceIte] <;> exact ⟨_, _, rfl⟩
  obtain ⟨v, u, hu⟩ := key
  have hc := (regs_complete s Rd Rn rd rn el a64 aa64 btype btn spe).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0)) s _ hc
  exact ⟨h1, v, congrArg Prod.fst h2, congrArg Prod.snd h2⟩

#print axioms regs
end Csel3

namespace Csinc3
set_option maxHeartbeats 400000 in
drive_spec regs_native, regs_complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd : BitVec 5)
      (rd : Rd.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (spe : s.regs.bank_Bool .SPESampleInFlight = false) =>
    ((do let _ ← (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 3#4 31#5 0#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0)) : SailM _) s

theorem regs (s : ArmBridge.Draft.NativeState) (Rd : BitVec 5) (rd : Rd.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (spe : s.regs.bank_Bool .SPESampleInFlight = false) (hRd : ¬ (Rd.toNat : Int) = 31) :
    (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 3#4 31#5 0#1 1#1 : SailM Unit) s =
      .ok () (ArmBridge.CruxCore.resSt s ((decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 3#4 31#5 0#1 1#1 : SailM Unit) s)) ∧
    ∃ v : BitVec 64, (ArmBridge.CruxCore.resSt s ((decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 3#4 31#5 0#1 1#1 : SailM Unit) s)).regs.gpr =
        s.regs.gpr.set (GPRSummary.key Rd.toNat).val v (GPRSummary.key Rd.toNat).isLt ∧
      (ArmBridge.CruxCore.resSt s ((decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 3#4 31#5 0#1 1#1 : SailM Unit) s)).regs.SP_EL0 = s.regs.SP_EL0 := by
  have key : ∃ (v : BitVec 64) (u : ArmBridge.Draft.NativeState), regs_native s Rd =
      .ok (s.regs.gpr.set (GPRSummary.key Rd.toNat).val v (GPRSummary.key Rd.toNat).isLt, s.regs.SP_EL0) u := by
    unfold regs_native
    simp only [hRd, spe, ite_true, ite_false, dite_eq_ite, ite_self]
    by_cases hc : s.regs.PSTATE.C = 1#1 <;> simp only [hc, ↓reduceIte] <;> exact ⟨_, _, rfl⟩
  obtain ⟨v, u, hu⟩ := key
  have hc := (regs_complete s Rd rd el a64 aa64 btype btn spe).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _ (fun u => (u.regs.gpr, u.regs.SP_EL0)) s _ hc
  exact ⟨h1, v, congrArg Prod.fst h2, congrArg Prod.snd h2⟩

#print axioms regs
end Csinc3


end HeapV2StepCerts.RegRoots
