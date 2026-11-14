-- (H-P13 (b) + H-P4, / a design decision): the generic shim + body composition. From the
-- shim entry's ShimInv, the shim pre-steps (plan_shim_class/mem/bl), the body under e17_general's deployment at
-- σ 7, the body's final RET back into the shim (plan_shim_ret; its target X30 = the BL link via e17_general) and
-- the shim post-steps, every ShimInv dit_window_shim needs is established along the actual run; then the DIT
-- window and restoration follow. BTI entry contract v1: direct BL caller.
-- Kept premises: fetch obligations, Profiles, the SUB/ADD SP class tails, the shim's offsets,
-- the slot static/separation facts, E17 closed membership for the shim map after the body (closed365),
-- the body's final SP (sp364), and the body DeploymentPremises at σ 7.
import RtDit3.ShimWindow
import RtShim2.ShimBranch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
open NativeEntryCallerParts ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option Elab.async false
namespace RtDit.Window
open RtDit RtDit.Shim HeapV2StepCerts

theorem next_placed {x : NativeState} {base : BitVec 64} {offS : Nat → BitVec 64} {j : Nat}
    (pc : x.regs._PC = base + offS j) (hs : offS (j + 1) = offS j + 4#64) :
    x.regs._PC + 4#64 = base + offS (j + 1) := by
  rw [pc, hs, BitVec.add_assoc]

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Window.dit_shim_run"
  (← IO.getStderr).flush

theorem dit_shim_run (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {pbase : Nat} {table : Nat → Prop}
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (codeSlot : ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes p mapping))
    (codeData : ImageTableSeparated scope loadBase mapping (MemNext.dataBytes p mapping))
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (e : NativeState)
    (room : 369 ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (straight : ∀ j, (j ≤ 5 ∨ (365 ≤ j ∧ j ≤ 367)) → offS (j + 1) = offS j + 4#64)
    (ret365 : offS 365 = offS 6 + 4#64)
    (inv0 : RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
      scope image loadBase base offS budget 0 e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent p mapping e)
    (spE : e.regs.SP_EL0 + BitVec.ofInt 64 (-16) = BitVec.ofNat 64 p.sp)
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (sep : ∀ a, RtShim2.ShimMem.slotBytes p mapping a → ¬ MemNext.dataBytes p mapping a)
    -- s0 BTI c (direct BL caller)
    (ob0 : FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word (stateAt real e 0))
    -- s1 SUB SP, SP, #16
    {w1 : BitVec 32} {writes1 : NativeEntry.Effects.Writes} {K1 : Int} {us1 : List (RegBind.Reg × RegBind.Upd)}
    (tail1 : RegVal.ClassTailVAt real w1 writes1 K1 (stateAt real e 1) ((stateAt real e 1).regs._PC + 4#64) us1)
    (hw1 : writes1.dit = false) (sub1 : RegBind.updOf us1 .sp = .set .sp (-16))
    (ob1 : FetchObligations spec config rows mapping w1 (stateAt real e 1))
    -- s2 MRS X9, DIT
    (prof2 : NativeEntryAdapters.MrsDit.Profile (stateAt real e 2))
    (ob2 : FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) (stateAt real e 2))
    -- s3 STP X9, X30, [SP]
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
    (bl7 : blTarget imm26 (stateAt real e 6) = base + offS 7)
    (low6 : (base + offS 7).toNat < 2 ^ 55)
    (ob6 : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) (stateAt real e 6))
    -- body: e17_general's deployment at σ 7, and its final RET back to s7
    (bodyBudget : Nat) (dp : DeploymentPremises spec config rows mapping base p (stateAt real e 7) bodyBudget)
    (hbB : 358 ≤ bodyBudget) (hbudget : budget - 365 = bodyBudget - 358)
    (low365 : (base + offS 365).toNat < 2 ^ 55)
    (sp364 : (stateAt real (stateAt real e 7) 357).regs.SP_EL0 = BitVec.ofNat 64 p.sp)
    (closed365 : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
      (ArmBridge.CruxGenGuarded.beforeFetchState (stateAt real e 365)))
    -- s7 LDP
    (ob365 : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7)
      (stateAt real e 365))
    -- s8 ADD SP, SP, #16 (keeps X9)
    {w8 : BitVec 32} {writes8 : NativeEntry.Effects.Writes} {K8 : Int} {us8 : List (RegBind.Reg × RegBind.Upd)}
    (tail8 : RegVal.ClassTailVAt real w8 writes8 K8 (stateAt real e 366) ((stateAt real e 366).regs._PC + 4#64) us8)
    (hw8 : writes8.dit = false) (keep9 : RegBind.updOf us8 (.x 9) = .keep)
    (ob8 : FetchObligations spec config rows mapping w8 (stateAt real e 366))
    -- s9 MSR DIT, X9
    (prof9 : NativeEntryAdapters.MsrDit.Profile (stateAt real e 367))
    (ob9 : FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) (stateAt real e 367))
    -- s10 RET
    (low10 : ((stateAt real e 368).regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55)
    (ob10 : FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) (stateAt real e 368)) :
    (∀ j, 5 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
      (stateAt real e 368).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧
      (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT := by
  have I : ∀ j, (j ≤ 6 ∨ (365 ≤ j ∧ j ≤ 368)) → j < budget := fun j h => by omega
  -- s0
  obtain ⟨f, r, i1, h1, m1, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 0 (I 0 (by omega)) page (aligned 0) _ _ _ _ (fun x => x.regs._PC + 4#64) e inv0 (NativeShimTails.btiC_tailVAt real e)
    (next_placed inv0.v2.v1.pc (straight 0 (by omega))) ob0
  have e1 : stateAt real e 1 = f := stateAt_succ_of r
  rw [← e1] at i1 h1 m1
  -- s1
  obtain ⟨f, r, i2, h2, m2, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 1 (I 1 (by omega)) page (aligned 1) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i1 tail1
    (next_placed i1.v2.v1.pc (straight 1 (by omega))) ob1
  have e2 : stateAt real e 2 = f := stateAt_succ_of r
  rw [← e2] at i2 h2 m2
  -- s2
  obtain ⟨f, r, i3, h3, m3, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 2 (I 2 (by omega)) page (aligned 2) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i2
    (NativeShimTails.mrsDit9_tailVAt real _ prof2) (next_placed i2.v2.v1.pc (straight 2 (by omega))) ob2
  have e3 : stateAt real e 3 = f := stateAt_succ_of r
  rw [← e3] at i3 h3 m3
  -- SP and slot presence at s3
  have sp1 : (stateAt real e 1).regs.SP_EL0 = e.regs.SP_EL0 := h1 .sp
  have sp2 : (stateAt real e 2).regs.SP_EL0 = (stateAt real e 1).regs.SP_EL0 + BitVec.ofInt 64 (-16) := by
    have h := h2 .sp; rw [sub1] at h; exact h
  have sp3 : (stateAt real e 3).regs.SP_EL0 = BitVec.ofNat 64 p.sp := by
    have h := h3 .sp
    have k : RegBind.updOf [(RegBind.Reg.x 9, RegBind.Upd.drop)] .sp = .keep := by decide
    rw [k] at h
    exact (h.trans (sp2.trans (by rw [sp1]; exact spE)))
  have slot3 : RtShim.SlotPrem.ShimSlotPresent p mapping (stateAt real e 3) := fun n hn i hi => by
    rw [m3, m2, m1]; exact slotE n hn i hi
  -- s3 STP
  obtain ⟨f, r, i4, _, _, k4, _⟩ := RtShim2.ShimMem.plan_shim_mem real spec config rows mapping _ p scope image
    loadBase separated base offS budget 3 (I 3 (by omega)) page (aligned 3) _ codeSlot _ _ _ _ (fun x => x.regs._PC + 4#64) _ i3 slot3 sp3
    (RtShim2.ShimMem.memS_Stp real spec config rows mapping static spAligned 9#5 30#5 (by decide) (by decide)
      (by decide +kernel) _) (next_placed i3.v2.v1.pc (straight 3 (by omega))) ob3
  have e4 : stateAt real e 4 = f := stateAt_succ_of r
  rw [← e4] at i4 k4
  -- s4
  obtain ⟨f, r, i5, _, m5, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 4 (I 4 (by omega)) page (aligned 4) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i4
    (NativeShimTails.ditOn_tailVAt real _ prof4) (next_placed i4.v2.v1.pc (straight 4 (by omega))) ob4
  have e5 : stateAt real e 5 = f := stateAt_succ_of r
  rw [← e5] at i5 m5
  -- s5
  obtain ⟨f, r, i6, _, m6, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 5 (I 5 (by omega)) page (aligned 5) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i5
    (NativeShimTails.isbSy_tailVAt real _ prof5) (next_placed i5.v2.v1.pc (straight 5 (by omega))) ob5
  have e6 : stateAt real e 6 = f := stateAt_succ_of r
  rw [← e6] at i6 m6
  -- s6 BL: the body entry σ 7 keeps the shim image placement; X30 = the BL link
  obtain ⟨f, r, i7, g7, _, m7, _⟩ := RtShim2.ShimBranch.plan_shim_bl real spec config rows mapping _ scope image
    loadBase separated base offS budget 6 (I 6 (by omega)) page (aligned 6) dp.nodup imm26 _ i6
    (by rw [bl7]; exact low6) controls6 offS budget 7 rfl bl7 ob6
  have e7 : stateAt real e 7 = f := stateAt_succ_of r
  rw [← e7] at i7 g7 m7
  have link : (stateAt real e 7).regs.gpr[30] = base + offS 365 := by
    rw [g7, Vector.getElem_set_self, i6.v2.v1.pc, ret365, BitVec.add_assoc]
  -- the body under e17_general, then its final RET (k = 357) back to s7
  have hE := e17_general real spec config rows mapping base p (stateAt real e 7) bodyBudget dp (by omega)
  have inv357 := (hE.1 357 (by omega)).1
  have x30 : (stateAt real (stateAt real e 7) 357).regs.gpr[(GPRSummary.key (30#5).toNat).val] = base + offS 365 :=
    hE.2.trans link
  have bodyMem := (dit_body_mem real spec config rows mapping base p (stateAt real e 7) bodyBudget dp (by omega)
    357 (by omega)).2
  obtain ⟨f, r, i365, _, spR, mR, _⟩ := RtShim2.ShimBranch.plan_shim_ret real spec config rows mapping _ _ _ _
    dp.static.separated base HeapV2Compose.offsetOf bodyBudget 357 (by omega) dp.page (by decide +kernel) 30#5
    (by decide) (by decide) _ (RtShim2.ShimBranch.shimInv_of_chainInv3 inv357.v3) (by rw [x30]; exact low365)
    offS budget 365 hbudget x30
    (MemNext.memFetch spec config rows mapping base bodyBudget 357 p (rowsFootprint spec.imageRows).byte dp.static
      0xc0 0xd65f03c0 (by decide +kernel) (by decide +kernel) _ (by decide) _ inv357.v3.v2)
  have s364 : stateAt real e 364 = stateAt real (stateAt real e 7) 357 := stateAt_add real e 7 357
  have e365 : stateAt real e 365 = f := by
    rw [show (365 : Nat) = 7 + 358 from rfl, stateAt_add real e 7 358]; exact stateAt_succ_of r
  rw [← e365] at i365 spR mR
  -- s7's invariant: the shim map (closed365) and the shim image placement carried across the body
  have placed365 : MemReloc.ImageOn scope image (stateAt real e 365) loadBase mapping :=
    HeapV2StepCerts.placed_class mR (HeapV2StepCerts.placed_class_writes bodyMem codeData i7.v2.placed)
  have J365 : RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
      scope image loadBase base offS budget 365 (stateAt real e 365) :=
    { v2 := ⟨i365.v2.v1, closed365, placed365, i365.v2.branch⟩, raw := i365.raw, noUpd := i365.noUpd,
      post2 := i365.post2, mode := i365.mode, debug := i365.debug, feat := i365.feat, dcache := i365.dcache }
  have sp365 : (stateAt real e 365).regs.SP_EL0 = BitVec.ofNat 64 p.sp := spR.trans sp364
  -- the slot from s3's STP to s7 (presence)
  obtain ⟨fS, rS, _, slot4, _⟩ := shim_stp real spec config rows mapping scope image loadBase base offS budget 3
    (I 3 (by omega)) page (aligned 3) _ i3 static sp3 spAligned ob3
  have eS : stateAt real e 4 = fS := stateAt_succ_of rS
  rw [← eS] at slot4
  have keepBody : ∀ n, mapping (BitVec.ofNat 64 p.sp) = some n → ∀ i < 16,
      (stateAt real e 365).mem[n + i]? = (stateAt real e 4).mem[n + i]? := by
    intro n hn i hi
    rw [mR, bodyMem (n + i) (sep _ ⟨n, hn, by omega, by omega⟩), m7, m6, m5]
  have present365 : RtShim.SlotPrem.ShimSlotPresent p mapping (stateAt real e 365) := fun n hn i hi => by
    rw [keepBody n hn i hi, slot4 n hn i hi]; rfl
  -- s7 LDP
  obtain ⟨f, r, i366, _, _, _, _⟩ := RtShim2.ShimMem.plan_shim_mem real spec config rows mapping _ p scope image
    loadBase separated base offS budget 365 (I 365 (by omega)) page (aligned 365) _ codeSlot _ _ _ _ (fun x => x.regs._PC + 4#64) _ J365
    present365 sp365
    (RtShim2.ShimMem.memS_Ldp real spec config rows mapping static spAligned 9#5 30#5 (by decide) (by decide)
      (by decide) (by decide +kernel) _) (next_placed J365.v2.v1.pc (straight 365 (by omega))) ob365
  have e366 : stateAt real e 366 = f := stateAt_succ_of r
  rw [← e366] at i366
  -- s8
  obtain ⟨f, r, i367, _, _, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 366 (I 366 (by omega)) page (aligned 366) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i366 tail8
    (next_placed i366.v2.v1.pc (straight 366 (by omega))) ob8
  have e367 : stateAt real e 367 = f := stateAt_succ_of r
  rw [← e367] at i367
  -- s9
  obtain ⟨f, r, i368, _, _, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 367 (I 367 (by omega)) page (aligned 367) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i367
    (NativeShimTails.msrDit9_tailVAt real _ prof9) (next_placed i367.v2.v1.pc (straight 367 (by omega))) ob9
  have e368 : stateAt real e 368 = f := stateAt_succ_of r
  rw [← e368] at i368
  -- the window
  have inv : ∀ j, (j ≤ 6 ∨ (365 ≤ j ∧ j ≤ 368)) →
      RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
        scope image loadBase base offS budget j (stateAt real e j) := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 365 ∨ j = 366 ∨ j = 367 ∨ j = 368
      by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact inv0
    · exact i1
    · exact i2
    · exact i3
    · exact i4
    · exact i5
    · exact i6
    · exact J365
    · exact i366
    · exact i367
    · exact i368
  exact dit_window_shim real spec config rows mapping scope image loadBase base offS budget e room page aligned inv
    ob0 tail1 hw1 ob1 prof2 ob2 static spAligned sp3 ob3 prof4 ob4 prof5 ob5 imm26 controls6
    (by rw [bl7]; exact low6) ob6
    (body_slot real spec config rows mapping base p e bodyBudget dp hbB (by rw [x30]; exact low365) sep)
    sp365 present365 ob365 tail8 hw8 keep9 ob8 prof9 ob9 (by decide +kernel) low10 ob10

#print axioms dit_shim_run
end RtDit.Window
