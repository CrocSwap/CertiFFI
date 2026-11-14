-- Memory ((B)): fetched-state → action-state transports for memory-class
-- premises. The action state is `actionState w sp K` with sp the PMU-event state
-- (E20Frame fetched.regs sp.regs). Registers read by the memory premises are untouched by
-- both E20 erasure and the action metadata; memory is equal.
import Bridge.CruxGenGuarded.EntryBtiNext
import ArmCertTranslateModel.CurrentProgramTransport
import MemM1.MemReadD2
import MemM1.MemWriteD6
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace HeapV2StepCerts.ActionTransport
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded

variable {fetched sp : NativeState} {w : BitVec 32} {K : Int}

theorem act {β : Type} (f : Regs → β) (hE : ∀ x, f (eraseE20 x) = f x)
    (hA : f (actionState w sp K).regs = f sp.regs) (e20 : E20Frame fetched.regs sp.regs) :
    f (actionState w sp K).regs = f fetched.regs :=
  hA.trans (frame_pres_E20 f hE e20)

theorem feat (e20 : E20Frame fetched.regs sp.regs) :
    (actionState w sp K).regs.FeatureImpl = fetched.regs.FeatureImpl :=
  act (fun r => r.FeatureImpl) (fun _ => rfl) rfl e20

theorem pstate (e20 : E20Frame fetched.regs sp.regs) :
    (actionState w sp K).regs.PSTATE = fetched.regs.PSTATE :=
  act (fun r => r.PSTATE) (fun _ => rfl) rfl e20

theorem gpr (e20 : E20Frame fetched.regs sp.regs) :
    (actionState w sp K).regs.gpr = fetched.regs.gpr :=
  act (fun r => r.gpr) (fun _ => rfl) rfl e20

theorem sp0 (e20 : E20Frame fetched.regs sp.regs) :
    (actionState w sp K).regs.SP_EL0 = fetched.regs.SP_EL0 :=
  act (fun r => r.SP_EL0) (fun _ => rfl) rfl e20

theorem b128 (e20 : E20Frame fetched.regs sp.regs) (k : Bank_BitVec_128) :
    (actionState w sp K).regs.bank_BitVec_128 k = fetched.regs.bank_BitVec_128 k :=
  act (fun r => r.bank_BitVec_128 k) (fun _ => rfl) rfl e20

/-- Bank_BitVec_64 keys outside the E20 counter set. -/
theorem b64 (e20 : E20Frame fetched.regs sp.regs) (k : Bank_BitVec_64)
    (hk : ∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k) :
    (actionState w sp K).regs.bank_BitVec_64 k = fetched.regs.bank_BitVec_64 k :=
  act (fun r => r.bank_BitVec_64 k) hk rfl e20

macro "e20key" : tactic => `(tactic| (intro x; simp (disch := decide) only [eraseE20, RegMap.set_ne]))

theorem mem (post : sp.mem = fetched.mem) : (actionState w sp K).mem = fetched.mem :=
  (actionState_mem w sp K).trans post

theorem current {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow}
    (e20 : E20Frame fetched.regs sp.regs) (post : sp.mem = fetched.mem)
    (cur : CurrentS1At spec config rows fetched) :
    CurrentS1At spec config rows (actionState w sp K) := by
  have m := mem (w := w) (K := K) post
  refine current_s1_program_write cur (fun _ => False)
    (fun a _ => by show (actionState w sp K).mem[a]? = fetched.mem[a]?; rw [m])
    (ArmBridge.CruxGenGuarded.EntryBtiNext.no_writes_separated _) (feat e20)
    (congrArg ProcState.EL (pstate e20)) (congrArg ProcState.nRW (pstate e20))
    (b64 e20 _ (by e20key)) (b64 e20 _ (by e20key)) (b64 e20 _ (by e20key)) (b64 e20 _ (by e20key))
    (b64 e20 _ (by e20key)) (b64 e20 _ (by e20key)) ?_ (fun _ => b64 e20 _ (by e20key))
    (fun _ => b64 e20 _ (by e20key)) (fun _ => b64 e20 _ (by e20key)) ?_
  · exact act (fun r => r.bank_Int .__supported_pa_size) (by e20key)
      (by simp (disch := decide) only [actionState, RegMap.set_ne]) e20
  · exact act (fun r => r.bank_Bool .__tlb_enabled) (by e20key)
      (by simp (disch := decide) only [actionState, RegMap.set_ne]) e20

theorem access {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query}
    (e20 : E20Frame fetched.regs sp.regs)
    (acc : CurrentS1AccessAt spec config rows mapping query data fetched) :
    CurrentS1AccessAt spec config rows mapping query data (actionState w sp K) :=
  current_s1_access_registers acc (feat e20) (b64 e20 _ (by e20key)) (b64 e20 _ (by e20key))
    (b128 e20 _) (b64 e20 _ (by e20key)) (b128 e20 _)
    (fun _ _ => act (fun r => r.bank_Int .__block_bbm_implemented) (by e20key)
      (by simp (disch := decide) only [actionState, RegMap.set_ne]) e20)

theorem mode (e20 : E20Frame fetched.regs sp.regs) (h : HostEL0ModeAt fetched.regs) :
    HostEL0ModeAt (actionState w sp K).regs := by
  have f := feat (w := w) (K := K) e20
  have p := pstate (w := w) (K := K) e20
  have scr := b64 (w := w) (K := K) e20 .SCR_EL3 (by e20key)
  have hcr := b64 (w := w) (K := K) e20 .HCR_EL2 (by e20key)
  exact ⟨f ▸ h.noEL2A32, f ▸ h.el2A64, f ▸ h.vhe, p ▸ h.el, scr ▸ h.ns, hcr ▸ h.tge⟩

theorem debug (e20 : E20Frame fetched.regs sp.regs) (h : ExistingE11DebugAt fetched.regs) :
    ExistingE11DebugAt (actionState w sp K).regs := by
  have mdscr := b64 (w := w) (K := K) e20 .MDSCR_EL1 (by e20key)
  have edscr : (actionState w sp K).regs.bank_BitVec_32 ._EDSCR = fetched.regs.bank_BitVec_32 ._EDSCR :=
    act (fun r => r.bank_BitVec_32 ._EDSCR) (by e20key)
      (by simp (disch := decide) only [actionState, RegMap.set_ne]) e20
  exact ⟨mdscr ▸ h.mde, edscr ▸ h.hde⟩

theorem post2 (e20 : E20Frame fetched.regs sp.regs) (h : MemM1.MemReadD2.PostRegs2 fetched.regs) :
    MemM1.MemReadD2.PostRegs2 (actionState w sp K).regs := by
  have f := feat (w := w) (K := K) e20
  have p := pstate (w := w) (K := K) e20
  have scr := b64 (w := w) (K := K) e20 .SCR_EL3 (by e20key)
  have hcr := b64 (w := w) (K := K) e20 .HCR_EL2 (by e20key)
  have sctlr := b64 (w := w) (K := K) e20 .SCTLR_EL2 (by e20key)
  have spe : (actionState w sp K).regs.bank_Bool .SPESampleInFlight = fetched.regs.bank_Bool .SPESampleInFlight :=
    act (fun r => r.bank_Bool .SPESampleInFlight) (by e20key)
      (by simp (disch := decide) only [actionState, RegMap.set_ne]) e20
  exact ⟨⟨spe ▸ h.post.spe, p ▸ h.post.el0, p ▸ h.post.nrw, f ▸ h.post.noRME, f ▸ h.post.vhe,
    f ▸ h.post.aa64el0, scr ▸ h.post.ns, hcr ▸ h.post.e2h, hcr ▸ h.post.tge, sctlr ▸ h.post.e0e⟩,
    f ▸ h.noMTE2⟩

theorem preW {acc : AccessDescriptor} (e20 : E20Frame fetched.regs sp.regs)
    (h : MemM1.MemWriteD6.PreW acc fetched.regs) : MemM1.MemWriteD6.PreW acc (actionState w sp K).regs := by
  have f := feat (w := w) (K := K) e20
  have p := pstate (w := w) (K := K) e20
  have scr := b64 (w := w) (K := K) e20 .SCR_EL3 (by e20key)
  have hcr := b64 (w := w) (K := K) e20 .HCR_EL2 (by e20key)
  have sctlr := b64 (w := w) (K := K) e20 .SCTLR_EL2 (by e20key)
  refine ⟨p ▸ h.el0, p ▸ h.nrw, f ▸ h.noRME, f ▸ h.vhe, f ▸ h.aa64el0, scr ▸ h.ns, hcr ▸ h.e2h,
    hcr ▸ h.tge, sctlr ▸ h.e0e, ?_⟩
  have tag := h.tag
  unfold MemM1.MemWriteD5.TagOK at tag ⊢
  rw [f]; exact tag

theorem dcache (e20 : E20Frame fetched.regs sp.regs) (h : currentDCache fetched.regs = true) :
    currentDCache (actionState w sp K).regs = true := by
  unfold currentDCache; rw [b64 e20 .SCTLR_EL2 (by e20key)]; exact h

theorem haft (e20 : E20Frame fetched.regs sp.regs) :
    hostHAFT (actionState w sp K).regs = hostHAFT fetched.regs := by
  unfold hostHAFT hostHA hostTCR2Enabled
  rw [feat e20, b64 e20 .TCR_EL2 (by e20key), b64 e20 .TCR2_EL2 (by e20key), b64 e20 .SCR_EL3 (by e20key)]

#print axioms current
#print axioms access
#print axioms haft
end HeapV2StepCerts.ActionTransport
