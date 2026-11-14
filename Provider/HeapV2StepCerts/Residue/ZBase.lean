-- Memory (H-P2): the per-step SIMD / flag step family over e17_general's deployment.
import HeapV2StepCerts.Residue.ZClass
import HeapV2StepCerts.E17General.Base
import HeapV2StepCerts.ScrubBind
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.ZSteps
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
set_option autoImplicit false

/-- One model step from an I4 state keeps the SIMD file, has the TST effect at 350 and the NZCV frame at 351..356. -/
def ZStep (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget k : Nat) : Prop :=
  ∀ x, I4 spec config rows mapping base pins entry budget k x →
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z ∧
      (k = 350 → HeapV2StepCerts.ValBind.VEff 350 x fin ∧
        fin.regs.PSTATE.N = 0#1 ∧ fin.regs.PSTATE.C = 0#1 ∧ fin.regs.PSTATE.V = 0#1) ∧
      (351 ≤ k → k ≤ 356 → HeapV2StepCerts.Flags.nzcv fin.regs = HeapV2StepCerts.Flags.nzcv x.regs)

/-- B1b: PSTATE.N = C = V = 0 on the states 351..357 (TST x1, #7 at 350; NZCV frames 351..356). -/
def NCVBind (k : Nat) (x : NativeState) : Prop :=
  351 ≤ k → k ≤ 357 → x.regs.PSTATE.N = 0#1 ∧ x.regs.PSTATE.C = 0#1 ∧ x.regs.PSTATE.V = 0#1

theorem ncv_init (x : NativeState) : NCVBind 0 x := fun h => absurd h (by decide)

theorem ncv_keep {k : Nat} {s f : NativeState} (lo : 351 ≤ k) (h : NCVBind k s)
    (fl : HeapV2StepCerts.Flags.nzcv f.regs = HeapV2StepCerts.Flags.nzcv s.regs) : NCVBind (k + 1) f := by
  intro _ hi
  obtain ⟨hn, hc, hv⟩ := h lo (by omega)
  simp only [HeapV2StepCerts.Flags.nzcv, Prod.mk.injEq] at fl
  exact ⟨fl.1.trans hn, fl.2.2.1.trans hc, fl.2.2.2.trans hv⟩

theorem ncv_out {k : Nat} (f : NativeState) (hk : k < 350 ∨ 357 ≤ k) : NCVBind (k + 1) f :=
  fun lo hi => absurd hk (by omega)

end HeapV2StepCerts.ZSteps
