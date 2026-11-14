import Bridge.AdcBridgeM
import Bridge.CruxIAdcs111
import Bridge.StepM
import Bridge.Boundary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
open ArmBridge.Draft
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to HeapV2StepCerts.SbcsFrameLNSym.
namespace HeapV2StepCerts.SbcsFrame

-- Memory (option (ii)): SBCS Xd, Xn, XZR register frame — only X[Rd] (and flags) change —

-- through the SDK's LNSym bridge (Bridge.AdcBridgeM.bridge_111 for ADCS 1/1/1 = SBCS 1/1/1 by

-- CruxIAdcs111.leaf_eq) and LNSym's exec_inst write frame, instead of a native root (kernel-heavy).

/-- formStep's epilogue (BTYPE, PC) leaves the action's GPRs and SP_EL0. -/
theorem formStep_regs (A : SailM Unit) (s a s' : NativeState) (hbt : s.regs.__BranchTaken = false)
    (hA : A s = .ok () a) (hf : ArmBridge.Boundary.formStep A s = .ok () s') :
    s'.regs.gpr = a.regs.gpr ∧ s'.regs.SP_EL0 = a.regs.SP_EL0 := by
  have w1 : (writeReg Register.__BranchTaken false : SailM Unit) s = .ok () s := by
    show EStateM.Result.ok () { s with regs := { s.regs with __BranchTaken := false } } = _
    rw [← hbt]
  unfold ArmBridge.Boundary.formStep at hf
  simp only [bind, EStateM.bind, w1, hA] at hf
  have rdPS : ∀ u : NativeState, (readReg Register.PSTATE : SailM ProcState) u = .ok u.regs.PSTATE u := fun _ => rfl
  have rdBTN : ∀ u : NativeState, (readReg Register.BTypeNext : SailM (BitVec 2)) u = .ok u.regs.BTypeNext u := fun _ => rfl
  have rdBT : ∀ u : NativeState, (readReg Register.__BranchTaken : SailM Bool) u = .ok u.regs.__BranchTaken u := fun _ => rfl
  have rdPC : ∀ u : NativeState, (readReg Register._PC : SailM (BitVec 64)) u = .ok u.regs._PC u := fun _ => rfl
  have wrPS : ∀ (v : ProcState) (u : NativeState), (writeReg Register.PSTATE v : SailM Unit) u =
      .ok () { u with regs := { u.regs with PSTATE := v } } := fun _ _ => rfl
  have wrPC : ∀ (v : BitVec 64) (u : NativeState), (writeReg Register._PC v : SailM Unit) u =
      .ok () { u with regs := { u.regs with _PC := v } } := fun _ _ => rfl
  simp only [rdPS, rdBTN, rdBT, rdPC, wrPS, wrPC] at hf
  split at hf
  · simp only [EStateM.bind, rdPC, wrPC, EStateM.Result.ok.injEq, true_and] at hf
    subst hf; exact ⟨rfl, rfl⟩
  · simp only [pure, EStateM.pure, EStateM.Result.ok.injEq, true_and] at hf
    subst hf; exact ⟨rfl, rfl⟩

theorem key_val' : ∀ n < 31, (GPRSummary.key n).val = n := by decide

end HeapV2StepCerts.SbcsFrame

