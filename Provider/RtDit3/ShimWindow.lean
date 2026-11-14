-- (H-P13/H-P19 + H-P4,): dit_window's shim hypotheses discharged from the shim states'
-- ShimInv (shim run indexing k = j, offset offS) by the actual shim steps (RtDit.Shim.*). Hypotheses are only
-- the step inputs: fetch obligations, Profiles, the two class tails (SUB/ADD SP), SP = p.sp at s3/s7,
-- slot static/presence, the BL/RET target bounds, and hbody (RtDit.Window.body_slot). s0 = BTI c via
-- btiC_tailVAt (no Profile). Generic; the synthetic instance follows the relink.
import RtDit2.Window
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
open NativeEntryCallerParts ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace RtDit.Window
open RtDit RtDit.Shim HeapV2StepCerts

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Window.dit_window_shim"
  (← IO.getStderr).flush

theorem dit_window_shim (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {pbase : Nat} {table : Nat → Prop}
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (e : NativeState)
    (room : 369 ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (inv : ∀ j, (j ≤ 6 ∨ (365 ≤ j ∧ j ≤ 368)) →
      RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
        scope image loadBase base offS budget j (stateAt real e j))
    -- s0 BTI c
    (ob0 : FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word (stateAt real e 0))
    -- s1 SUB SP, SP, #16
    {w1 : BitVec 32} {writes1 : NativeEntry.Effects.Writes} {K1 : Int} {next1 : BitVec 64}
    {us1 : List (RegBind.Reg × RegBind.Upd)}
    (tail1 : RegVal.ClassTailVAt real w1 writes1 K1 (stateAt real e 1) next1 us1) (hw1 : writes1.dit = false)
    (ob1 : FetchObligations spec config rows mapping w1 (stateAt real e 1))
    -- s2 MRS X9, DIT
    (prof2 : NativeEntryAdapters.MrsDit.Profile (stateAt real e 2))
    (ob2 : FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) (stateAt real e 2))
    -- s3 STP X9, X30, [SP] and s7 LDP X9, X30, [SP]: the slot at SP = p.sp
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (sp3 : (stateAt real e 3).regs.SP_EL0 = BitVec.ofNat 64 p.sp)
    (ob3 : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7)
      (stateAt real e 3))
    -- s4 MSR DIT, #1
    (prof4 : NativeEntryAdapters.DitOn.Profile (stateAt real e 4))
    (ob4 : FetchObligations spec config rows mapping NativeEntryDispatch.DitOn.word (stateAt real e 4))
    -- s5 ISB
    (prof5 : NativeEntryAdapters.IsbSy.Profile (stateAt real e 5))
    (ob5 : FetchObligations spec config rows mapping NativeEntryDispatch.IsbSy.word (stateAt real e 5))
    -- s6 BL body
    (imm26 : BitVec 26) (controls6 : CallerControls (stateAt real e 6))
    (low6 : (blTarget imm26 (stateAt real e 6)).toNat < 2 ^ 55)
    (ob6 : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) (stateAt real e 6))
    -- body (states 7..365, incl. its final RET): RtDit.Window.body_slot
    (hbody : ∀ j, 7 ≤ j → j ≤ 365 → (stateAt real e j).regs.PSTATE.DIT = (stateAt real e 7).regs.PSTATE.DIT ∧
      SlotKeep p mapping (stateAt real e 7) (stateAt real e j))
    -- s7 LDP
    (sp365 : (stateAt real e 365).regs.SP_EL0 = BitVec.ofNat 64 p.sp)
    (present365 : RtShim.SlotPrem.ShimSlotPresent p mapping (stateAt real e 365))
    (ob365 : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7)
      (stateAt real e 365))
    -- s8 ADD SP, SP, #16 (keeps X9)
    {w8 : BitVec 32} {writes8 : NativeEntry.Effects.Writes} {K8 : Int} {next8 : BitVec 64}
    {us8 : List (RegBind.Reg × RegBind.Upd)}
    (tail8 : RegVal.ClassTailVAt real w8 writes8 K8 (stateAt real e 366) next8 us8) (hw8 : writes8.dit = false)
    (keep9 : RegBind.updOf us8 (.x 9) = .keep)
    (ob8 : FetchObligations spec config rows mapping w8 (stateAt real e 366))
    -- s9 MSR DIT, X9
    (prof9 : NativeEntryAdapters.MsrDit.Profile (stateAt real e 367))
    (ob9 : FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) (stateAt real e 367))
    -- s10 RET
    (noEret10 : (Sail.BitVec.extractLsb (EntryBodyRet.W 30#5) 31 12 == 879088#20) = false)
    (low10 : ((stateAt real e 368).regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55)
    (ob10 : FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) (stateAt real e 368)) :
    (∀ j, 5 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
      (stateAt real e 368).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧
      (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT := by
  have I : ∀ j, (j ≤ 6 ∨ (365 ≤ j ∧ j ≤ 368)) → j < budget := fun j h => by omega
  refine dit_window real p mapping e ?_ ?_ ?_ ?_ ?_ ?_ ?_ hbody ?_ ?_ ?_ ?_
  · obtain ⟨fin, run, d, _⟩ := shim_class real spec config rows mapping _ scope image loadBase base offS budget 0
      (I 0 (by omega)) page (aligned 0) _ (inv 0 (by omega)) (NativeShimTails.btiC_tailVAt real _) rfl ob0
    exact ⟨fin, run, d⟩
  · obtain ⟨fin, run, d, _⟩ := shim_class real spec config rows mapping _ scope image loadBase base offS budget 1
      (I 1 (by omega)) page (aligned 1) _ (inv 1 (by omega)) tail1 hw1 ob1
    exact ⟨fin, run, d⟩
  · obtain ⟨fin, run, x9, d, _⟩ := shim_mrs9 real spec config rows mapping _ scope image loadBase base offS budget 2
      (I 2 (by omega)) page (aligned 2) _ (inv 2 (by omega)) prof2 ob2
    exact ⟨fin, run, x9, d⟩
  · obtain ⟨fin, run, d, slot, _⟩ := shim_stp real spec config rows mapping scope image loadBase base offS budget 3
      (I 3 (by omega)) page (aligned 3) _ (inv 3 (by omega)) static sp3 spAligned ob3
    exact ⟨fin, run, d, slot⟩
  · obtain ⟨fin, run, d, m, _⟩ := shim_ditOn real spec config rows mapping _ scope image loadBase base offS budget 4
      (I 4 (by omega)) page (aligned 4) _ (inv 4 (by omega)) prof4 ob4
    exact ⟨fin, run, d, m⟩
  · obtain ⟨fin, run, d, m, _⟩ := shim_class real spec config rows mapping _ scope image loadBase base offS budget 5
      (I 5 (by omega)) page (aligned 5) _ (inv 5 (by omega)) (NativeShimTails.isbSy_tailVAt real _ prof5) rfl ob5
    exact ⟨fin, run, d, m⟩
  · exact shim_bl real spec config rows mapping _ scope image loadBase base offS budget 6
      (I 6 (by omega)) page (aligned 6) _ (inv 6 (by omega)) imm26 controls6 low6 ob6
  · exact shim_ldp real spec config rows mapping scope image loadBase base offS budget 365
      (I 365 (by omega)) page (aligned 365) _ (inv 365 (by omega)) static sp365 spAligned present365 ob365
  · obtain ⟨fin, run, d, _, holds⟩ := shim_class real spec config rows mapping _ scope image loadBase base offS
      budget 366 (I 366 (by omega)) page (aligned 366) _ (inv 366 (by omega)) tail8 hw8 ob8
    exact ⟨fin, run, d, RtSaved.kept_reg holds ⟨9, by decide⟩ keep9⟩
  · exact shim_msr9 real spec config rows mapping _ scope image loadBase base offS budget 367
      (I 367 (by omega)) page (aligned 367) _ (inv 367 (by omega)) prof9 ob9 |>.imp fun _ h => ⟨h.1, h.2.1⟩
  · obtain ⟨fin, run, d, _⟩ := shim_ret real spec config rows mapping _ scope image loadBase base offS budget 368
      (I 368 (by omega)) page (aligned 368) _ (inv 368 (by omega)) 30#5 (by decide) noEret10 low10 ob10
    exact ⟨fin, run, d⟩

#print axioms dit_window_shim
end RtDit.Window
