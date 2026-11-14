import PairDefault236.Current
import HeapV2StepCerts.ActionTransport
import TranslateSpan.DefaultFiniteMem
import NativeTagCheck.Tail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option Elab.async false
namespace PairDefault236

/-- Transport exactly the control registers and checked queries used by an
actual memory action through its instruction-spec PMU and metadata prefix. -/
theorem Current.At.action {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : Current.Consumer} {catalogue : NativeMteTagCheck.ControlCatalogue} {fetched sp : NativeState} (w : BitVec 32) (K : Int)
    (h : Current.At spec config rows mapping m catalogue fetched)
    (e20 : E20Frame fetched.regs sp.regs) (mem : sp.mem = fetched.mem) :
    Current.At spec config rows mapping m catalogue (actionState w sp K) := by
  have f := ActionTransport.feat (w := w) (K := K) e20
  have p := ActionTransport.pstate (w := w) (K := K) e20
  have scr := ActionTransport.b64 (w := w) (K := K) e20 .SCR_EL3 (by e20key)
  have hcr := ActionTransport.b64 (w := w) (K := K) e20 .HCR_EL2 (by e20key)
  have sctlr := ActionTransport.b64 (w := w) (K := K) e20 .SCTLR_EL2 (by e20key)
  have spe : (actionState w sp K).regs.bank_Bool .SPESampleInFlight =
      fetched.regs.bank_Bool .SPESampleInFlight :=
    ActionTransport.act (fun r => r.bank_Bool .SPESampleInFlight) (by e20key)
      (by simp (disch := decide) only [actionState, RegMap.set_ne]) e20
  refine ⟨?_,ActionTransport.current e20 mem h.current, ActionTransport.mode e20 h.mode,
    ⟨spe ▸ h.post.spe,p ▸ h.post.el0,p ▸ h.post.nrw,f ▸ h.post.noRME,f ▸ h.post.vhe,
      f ▸ h.post.aa64el0,scr ▸ h.post.ns,hcr ▸ h.post.e2h,hcr ▸ h.post.tge,sctlr ▸ h.post.e0e⟩,
    ActionTransport.debug e20 h.debug, ActionTransport.dcache e20 h.dcache,
    ActionTransport.mem (w := w) (K := K) mem ▸ h.raw,?_,?_⟩
  · intro va acc aligned n permitted
    obtain ⟨q,hva,hacc,hal,hn,member,data,access⟩ := h.closed va acc aligned n permitted
    exact ⟨q,hva,hacc,hal,hn,member,data,ActionTransport.access e20 access⟩
  · intro wr acc shape
    rw [ActionTransport.haft e20]
    exact h.noUpd wr acc shape
  · have tcr := ActionTransport.b64 (w := w) (K := K) e20 .TCR_EL2 (by e20key)
    rcases h.controls with ⟨host,tco,tcf,prep⟩
    refine ⟨⟨p ▸ host.el,p ▸ host.nrw,f ▸ host.aa64,f ▸ host.rme,f ▸ host.vhe,
      scr ▸ host.ns,hcr ▸ host.e2h,hcr ▸ host.tge⟩,p ▸ tco,sctlr ▸ tcf,?_⟩
    exact ⟨tcr.trans prep.1,sctlr.trans prep.2.1,hcr.trans prep.2.2.1,scr.trans prep.2.2.2⟩

#print axioms Current.At.action
end PairDefault236

namespace PairDefault236
open ArmBridge.Draft NativeMteTagCheck
structure Ctx {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : Current.Consumer) (catalogue : ControlCatalogue) (cost : Nat) (X : NativeState → Prop) (x : NativeState) : Prop where
  current : Current.At spec config rows mapping m catalogue x
  prog : X x
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  statusRows : TagStatusRows x (x.choiceOcc.getD 1354 0) cost

theorem Ctx.of_finite {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : Current.Consumer} {catalogue : ControlCatalogue} {cost : Nat} {X : NativeState → Prop} {x : NativeState}
    (h : TranslateSpan.DefaultEntryMem.FiniteFetchCtx spec config rows mapping m X catalogue cost x) :
    Ctx spec config rows mapping m catalogue cost X x :=
  ⟨⟨h.closed,h.current,h.mode,h.post,h.debug,h.dcache,h.raw,h.noUpd,h.controls⟩,h.prog,h.feat,h.statusRows⟩
end PairDefault236
