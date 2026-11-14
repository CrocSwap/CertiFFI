-- RtPremC.PremC: run-level premise C (closed365, low365) derived; shim_chain' consumes it.
-- split of shim_release_v2, part A2 = shim_chain (body + epilogue, from shim_pre).
-- Was shim_release_v2 = shim_release with `sep`/code separation stated against
-- Core's exact Residue.StoreBytes (ct2Residue_run's frame; accPA's +8 half is 8 bytes) instead of MemNext.dataBytes
-- (whose +8 half over-covers 8 bytes past a pair), and sp364 derived (ct2Residue_run SP + the prologue). Was: (H-P13 → certiffi's release headline, e4953b32 + shimData fix): Release.ShimPrologue and
-- Release.ShimEpilogue from the actual shim run. shim_release establishes, along stateAt e: the shim's ShimInv
-- chain (plan_shim_*), the body under e17_general at σ 7 (DeploymentPremises premise: bodyPremises_of),
-- the body's final RET back to s7 (call/return; X30 = the BL link), the epilogue, and the caller return at 369
-- (s10 RET to X30 = e's X30 = callerPC + 4, the caller contract). Fields: steps, E17 (shimMap) at shim states and
-- 369, EvShape per shim step and the body RET (RtDit.ShimEv), PCs (offS = shimPC), DIT window/restoration,
-- SP/X30 frame (slot round trip), qBody (X2/X3 kept), ditBody.
import RtDit6.ShimChain
import RtPremC.CtlBody
import ArmCertTranslateModel.E26Binding
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
open NativeEntryCallerParts ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option Elab.async false
namespace RtPremC
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts RtDit.Release
open ArmBridge.CruxGenGuarded.Release (shimPC shimData shimMap ShimPrologue ShimEpilogue)

/-- Run-level premise C: shim_chain's σ365 facts. -/
structure RunPremisesC (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) (base : BitVec 64) (offS : Nat → BitVec 64) (e : NativeState) : Prop where
  low365 : (base + offS 365).toNat < 2 ^ 55
  closed365 : ClosedMembershipAt spec config rows mapping (shimMap spec mapping base pins)
    (ArmBridge.CruxGenGuarded.beforeFetchState (stateAt real e 365))

theorem ctl_bff (s : NativeState) : ctlv (ArmBridge.CruxGenGuarded.beforeFetchState s).regs = ctlv s.regs := by
  simp (disch := decide) only [ctlv, ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]

theorem mem_bff (s : NativeState) : (ArmBridge.CruxGenGuarded.beforeFetchState s).mem = s.mem := rfl

/-- The σ7 shim-map closure survives the body: translation controls and descriptor bytes are unchanged. -/
theorem closed_across {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {s t : NativeState}
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (rel : CtlRel spec s t) :
    ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState t) := by
  have hc : ctlv (ArmBridge.CruxGenGuarded.beforeFetchState t).regs = ctlv (ArmBridge.CruxGenGuarded.beforeFetchState s).regs :=
    (ctl_bff t).trans (rel.1.trans (ctl_bff s).symm)
  simp only [ctlv, Prod.mk.injEq] at hc
  obtain ⟨feat, el, nrw, tlb, ⟨tcr, tcr2, hcr, scr, sctlr, mair, httbr, pir, pire0, por⟩, ⟨ttbr0, ttbr1⟩, pa, bbm⟩ := hc
  refine ArmCert.Translate.Model.closed_membership_across_interval closed ⟨?_, ttbr0, httbr, ttbr1⟩
    ⟨feat, el, nrw, tcr, tcr2, hcr, scr, sctlr, mair, pa, fun _ => pir, fun _ => pire0, fun _ => por, tlb, fun _ => bbm⟩
  intro a ha
  rw [mem_bff, mem_bff]
  exact rel.2 a ha

/-- Premise C from shim_pre's conclusion, the body's deployment premises and offPost: no σ k premise beyond those. -/
theorem runPremisesC (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (e : NativeState)
    (offPost : ∀ j, 365 ≤ j → j ≤ 368 → offS j = shimPC (j - 358))
    (pre : ShimPre real spec config rows mapping pins scope image loadBase base offS budget e)
    (bodyBudget : Nat) (dp : DeploymentPremises spec config rows mapping base pins (stateAt real e 7) bodyBudget)
    (hbB : 358 ≤ bodyBudget) :
    RunPremisesC real spec config rows mapping pins base offS e := by
  have low365 : (base + offS 365).toNat < 2 ^ 55 := by
    rw [offPost 365 (by omega) (by omega), show 365 - 358 = 7 from rfl]
    have hb := dp.low
    rw [BitVec.toNat_add]
    simp only [shimPC, BitVec.toNat_ofNat]
    omega
  refine ⟨low365, ?_⟩
  have hE := e17_general real spec config rows mapping base pins (stateAt real e 7) bodyBudget dp (by omega)
  have x30 : ((stateAt real (stateAt real e 7) 357).regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55 := by
    rw [hE.2.trans pre.x30_7]; exact low365
  have rel := ctl_body_ret real spec config rows mapping base pins (stateAt real e 7) bodyBudget dp hbB x30
  have e365 : stateAt real e 365 = stateAt real (stateAt real e 7) 358 := RtDit.Window.stateAt_add real e 7 358
  rw [e365]
  exact closed_across pre.inv7.v2.closed rel

theorem shim_chain' (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (codeSlot : ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (codeStore : ImageTableSeparated scope loadBase mapping (Residue.StoreBytes pins mapping))
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (e : NativeState) (callerPC : BitVec 64)
    (agrees : ConsumerMapAgrees spec mapping (shimMap spec mapping base pins))
    (room : 369 ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC j) (offPost : ∀ j, 365 ≤ j → j ≤ 368 → offS j = shimPC (j - 358))
    (inv0 : RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins)
      scope image loadBase base offS budget 0 e)
    (callerX30 : e.regs.gpr[30] = callerPC + 4#64)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)
    (sep : ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → ¬ Residue.StoreBytes pins mapping a)
    (ob0 : FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word (stateAt real e 0))
    {w1 : BitVec 32} {writes1 : NativeEntry.Effects.Writes} {K1 : Int} {us1 : List (RegBind.Reg × RegBind.Upd)}
    (tail1 : RegValE.ClassTailVAt real w1 writes1 K1 (stateAt real e 1) ((stateAt real e 1).regs._PC + 4#64) us1)
    (hw1 : writes1.dit = false) (sub1 : RegBind.updOf us1 .sp = .set .sp (-16))
    (keep1all : ∀ i : Fin 31, RegBind.updOf us1 (.x i) = .keep)
    (ob1 : FetchObligations spec config rows mapping w1 (stateAt real e 1))
    (prof2 : NativeEntryAdapters.MrsDit.Profile (stateAt real e 2))
    (ob2 : FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) (stateAt real e 2))
    (ob3 : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7)
      (stateAt real e 3))
    (prof4 : NativeEntryAdapters.DitOn.Profile (stateAt real e 4))
    (ob4 : FetchObligations spec config rows mapping NativeEntryDispatch.DitOn.word (stateAt real e 4))
    (prof5 : NativeEntryAdapters.IsbSy.Profile (stateAt real e 5))
    (ob5 : FetchObligations spec config rows mapping NativeEntryDispatch.IsbSy.word (stateAt real e 5))
    (imm26 : BitVec 26) (controls6 : CallerControls (stateAt real e 6))
    (bl7 : blTarget imm26 (stateAt real e 6) = base + offS 7)
    (low6 : (base + offS 7).toNat < 2 ^ 55)
    (ob6 : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) (stateAt real e 6))
    (bodyBudget : Nat) (dp : DeploymentPremises spec config rows mapping base pins (stateAt real e 7) bodyBudget)
    (hbB : 358 ≤ bodyBudget) (hbudget : budget - 365 = bodyBudget - 358)
    (pre : ShimPre real spec config rows mapping pins scope image loadBase base offS budget e)
    (ob365 : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7)
      (stateAt real e 365))
    {w8 : BitVec 32} {writes8 : NativeEntry.Effects.Writes} {K8 : Int} {us8 : List (RegBind.Reg × RegBind.Upd)}
    (tail8 : RegValE.ClassTailVAt real w8 writes8 K8 (stateAt real e 366) ((stateAt real e 366).regs._PC + 4#64) us8)
    (hw8 : writes8.dit = false) (add8 : RegBind.updOf us8 .sp = .set .sp 16)
    (keep8all : ∀ i : Fin 31, RegBind.updOf us8 (.x i) = .keep)
    (ob8 : FetchObligations spec config rows mapping w8 (stateAt real e 366))
    (prof9 : NativeEntryAdapters.MsrDit.Profile (stateAt real e 367))
    (ob9 : FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) (stateAt real e 367))
    (low10 : (callerPC + 4#64).toNat < 2 ^ 55)
    (ob10 : FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) (stateAt real e 368)) :
    ShimChain real spec config rows mapping pins scope image loadBase base offS budget e callerPC  := by
  have C := runPremisesC real spec config rows mapping pins scope image loadBase base offS budget e offPost pre
    bodyBudget dp hbB
  exact shim_chain real spec config rows mapping pins scope image loadBase separated codeSlot codeStore base offS budget e
    callerPC agrees room page aligned offPre offPost inv0 callerX30 slotE spE static spAligned sep ob0 tail1 hw1 sub1
    keep1all ob1 prof2 ob2 ob3 prof4 ob4 prof5 ob5 imm26 controls6 bl7 low6 ob6 bodyBudget dp hbB hbudget C.low365
    C.closed365 pre ob365 tail8 hw8 add8 keep8all ob8 prof9 ob9 low10 ob10

#print axioms closed_across
#print axioms runPremisesC
#print axioms shim_chain'
end RtPremC
