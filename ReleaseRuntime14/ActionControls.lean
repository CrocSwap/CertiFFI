-- Transfer ordinary memory and TCO control facts through the actual E20 frame.
import CurrentInv
import HeapV2StepCerts.ActionTransport

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open HeapV2StepCerts.ActionTransport

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.ActionControls

variable {fetched sp : NativeState} {w : BitVec 32} {K : Int}

theorem post (e20 : E20Frame fetched.regs sp.regs) (h : MemM1.MemReadD.PostRegs fetched.regs) :
    MemM1.MemReadD.PostRegs (actionState w sp K).regs := by
  have f := feat (w := w) (K := K) e20
  have p := pstate (w := w) (K := K) e20
  have scr := b64 (w := w) (K := K) e20 .SCR_EL3 (by e20key)
  have hcr := b64 (w := w) (K := K) e20 .HCR_EL2 (by e20key)
  have sctlr := b64 (w := w) (K := K) e20 .SCTLR_EL2 (by e20key)
  have spe : (actionState w sp K).regs.bank_Bool .SPESampleInFlight = fetched.regs.bank_Bool .SPESampleInFlight :=
    act (fun r => r.bank_Bool .SPESampleInFlight) (by e20key)
      (by simp (disch := decide) only [actionState, RegMap.set_ne]) e20
  exact ⟨spe ▸ h.spe, p ▸ h.el0, p ▸ h.nrw, f ▸ h.noRME, f ▸ h.vhe,
    f ▸ h.aa64el0, scr ▸ h.ns, hcr ▸ h.e2h, hcr ▸ h.tge, sctlr ▸ h.e0e⟩

theorem tco (e20 : E20Frame fetched.regs sp.regs)
    (h : MemM1.MemReadD.PostRegs fetched.regs)
    (mte2 : fetched.regs.FeatureImpl[134] = true) (tco : fetched.regs.PSTATE.TCO = 1#1) :
    NativeMte2.TcoAt (actionState w sp K) := by
  apply ReleaseProfile.tcoAt _ (post e20 h)
  · rw [feat (w := w) (K := K) e20]; exact mte2
  · rw [pstate (w := w) (K := K) e20]; exact tco

#print axioms post
#print axioms tco
end ReleaseProfile.ActionControls
