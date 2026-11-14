-- RtShimG.BodyContract: what the shim chain
-- needs from the body it calls, for a body of any length L, plus the heap-v2 instance (L = 357) from
-- DeploymentPremises via e17_general / Residue.Run.{residue_general, ct2Residue_run} / dit_body_{mem,ret}.
import RtDit6.ShimChain
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
open NativeEntryCallerParts ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option Elab.async false
namespace RtShimG
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts

/-- The body contract at the body's entry state s7 (= the shim's state 7): the body (length L, in its own code
coordinates bm/bscope/bimage/bloadBase/bodyOff/bodyBudget) ends at a RET x30 whose fetch is valid, returns x30, SP and
the callee-saved registers, keeps DIT on every body state and the RET, and touches no memory outside Store. -/
structure BodyContract (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (bm : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (bscope : Nat → Prop) (bimage : MemReloc.Image) (bloadBase : MemReloc.Word)
    (base : BitVec 64) (bodyOff : Nat → BitVec 64) (bodyBudget : Nat)
    (L : Nat) (Store : Nat → Prop) (calleeSaved : List (Fin 31)) (s7 : NativeState) : Prop where
  invRet : RtShim2.ShimInv spec config rows mapping bm bscope bimage bloadBase base bodyOff bodyBudget L
    (stateAt real s7 L)
  sepRet : ImageTableSeparated bscope bloadBase mapping (rowsFootprint spec.imageRows).byte
  pageRet : base.toNat % 4096 = 0
  alignRet : (bodyOff L).toNat % 4 = 0
  budgetRet : L < bodyBudget
  fetchRet : Nonempty (FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) (stateAt real s7 L))
  x30 : (stateAt real s7 L).regs.gpr[(GPRSummary.key (30#5).toNat).val] = s7.regs.gpr[30]
  sp : (stateAt real s7 L).regs.SP_EL0 = s7.regs.SP_EL0
  keep : ∀ r ∈ calleeSaved, (stateAt real s7 L).regs.gpr[r.val] = s7.regs.gpr[r.val]
  dit : ∀ j, j ≤ L → (stateAt real s7 j).regs.PSTATE.DIT = s7.regs.PSTATE.DIT
  ditRet : ((stateAt real s7 L).regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55 →
    (stateAt real s7 (L + 1)).regs.PSTATE.DIT = s7.regs.PSTATE.DIT
  memFrame : ∀ j, j ≤ L → ∀ a, ¬ Store a → (stateAt real s7 j).mem[a]? = s7.mem[a]?

run_cmd do
  IO.eprintln "CURRENT_DECL RtShimG.bodyContract_heapv2"
  (← IO.getStderr).flush

/-- heap-v2 instance: the body under DeploymentPremises (L = 357, Store = Residue.StoreBytes, callee-saved =
Residue.frameRegs = X18, X20..X29). -/
theorem bodyContract_heapv2 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (s7 : NativeState) (bodyBudget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins s7 bodyBudget) (hbB : 358 ≤ bodyBudget) :
    BodyContract real spec config rows mapping (cmap spec mapping base pins) HeapV2StepCerts.codeScope
      (HeapV2.image base) base base HeapV2Compose.offsetOf bodyBudget 357 (Residue.StoreBytes pins mapping)
      Residue.frameRegs s7 := by
  have hE := e17_general real spec config rows mapping base pins s7 bodyBudget dp (by omega)
  have inv357 := (hE.1 357 (by omega)).1
  have hRes := HeapV2StepCerts.Residue.Run.residue_general real spec config rows mapping base pins s7 bodyBudget dp
    (by omega)
  have hCT := HeapV2StepCerts.Residue.Run.ct2Residue_run real spec config rows mapping base pins s7 bodyBudget dp
    (by omega)
  exact
    { invRet := RtShim2.ShimBranch.shimInv_of_chainInv3 inv357.v3
      sepRet := dp.static.separated
      pageRet := dp.page
      alignRet := by decide +kernel
      budgetRet := by omega
      fetchRet := ⟨MemNext.memFetch spec config rows mapping base bodyBudget 357 pins
        (rowsFootprint spec.imageRows).byte dp.static 0xc0 0xd65f03c0 (by decide +kernel) (by decide +kernel)
        (EntryBodyRet.W 30#5) (by decide) _ inv357.v3.v2⟩
      x30 := hE.2
      sp := hCT.2.2.2.1
      keep := fun r hr => by simpa [RegBind.regVal] using hCT.1 r hr
      dit := fun j hj => (dit_body_mem real spec config rows mapping base pins s7 bodyBudget dp (by omega) j hj).1
      ditRet := fun h => (dit_body_ret real spec config rows mapping base pins s7 bodyBudget dp hbB h).1
      memFrame := fun j hj => (hRes j hj).2.1.2 }

#print axioms bodyContract_heapv2
end RtShimG
