import HeapV2StepCerts.ActionTransport
import NativeTagCheck.Tail

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open HeapV2StepCerts.ActionTransport
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultActionControls

theorem controls_of_sys {s t : NativeState} {catalogue : NativeMteTagCheck.ControlCatalogue}
    (controls : NativeMteTagCheck.DefaultAt catalogue s) (sys : SysEq2 s.regs t.regs)
    (tco : t.regs.PSTATE.TCO = s.regs.PSTATE.TCO) : NativeMteTagCheck.DefaultAt catalogue t := by
  refine ⟨⟨sys.el ▸ controls.host.el,sys.nrw ▸ controls.host.nrw,
    sys.feat ▸ controls.host.aa64,sys.feat ▸ controls.host.rme,
    sys.feat ▸ controls.host.vhe,sys.scr ▸ controls.host.ns,
    sys.hcr ▸ controls.host.e2h,sys.hcr ▸ controls.host.tge⟩,
    tco.trans controls.tco,sys.sctlr ▸ controls.tcf0,?_⟩
  obtain ⟨tcr,sctlr,hcr,scr⟩ := controls.preparation
  exact ⟨sys.tcr.trans tcr,sys.sctlr.trans sctlr,sys.hcr.trans hcr,sys.scr.trans scr⟩

#check "CURRENT_DECL default metadata controls"
theorem default_at {fetched sp : NativeState} {w : BitVec 32} {K : Int}
    {catalogue : NativeMteTagCheck.ControlCatalogue} (e20 : E20Frame fetched.regs sp.regs)
    (controls : NativeMteTagCheck.DefaultAt catalogue fetched) :
    NativeMteTagCheck.DefaultAt catalogue (actionState w sp K) := by
  have f := feat (w := w) (K := K) e20
  have p := pstate (w := w) (K := K) e20
  have scr := b64 (w := w) (K := K) e20 .SCR_EL3 (by e20key)
  have hcr := b64 (w := w) (K := K) e20 .HCR_EL2 (by e20key)
  have sctlr := b64 (w := w) (K := K) e20 .SCTLR_EL2 (by e20key)
  have tcr := b64 (w := w) (K := K) e20 .TCR_EL2 (by e20key)
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · rw [p]; exact controls.host.el
  · rw [p]; exact controls.host.nrw
  · rw [f]; exact controls.host.aa64
  · rw [f]; exact controls.host.rme
  · rw [f]; exact controls.host.vhe
  · rw [scr]; exact controls.host.ns
  · rw [hcr]; exact controls.host.e2h
  · rw [hcr]; exact controls.host.tge
  · rw [p]; exact controls.tco
  · rw [sctlr]; exact controls.tcf0
  · unfold NativeMteTagCheck.PreparationAt
    rw [tcr,sctlr,hcr,scr]
    exact controls.preparation

#print axioms default_at
#print axioms controls_of_sys
end ReleaseProfile.DefaultActionControls
