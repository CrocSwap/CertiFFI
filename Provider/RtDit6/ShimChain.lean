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
import RtDit6.ShimPre
import HeapV2StepCerts.Residue.RAssembly
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
namespace RtDit.Release
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts
open ArmBridge.CruxGenGuarded.Release (shimPC shimData shimMap ShimPrologue ShimEpilogue)

/-- The shared facts of the actual shim + body run (the split of shim_release_v2,): established once
by shim_chain, consumed by the ShimPrologue / ShimEpilogue halves and by ShimKeep. -/
structure ShimChain (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (e : NativeState) (callerPC : BitVec 64) : Prop where
  runs : ∀ j, (j ≤ 6 ∨ (364 ≤ j ∧ j ≤ 368)) → modelStep real (stateAt real e j) = .ok () (stateAt real e (j + 1))
  inv : ∀ j, (j ≤ 6 ∨ (365 ≤ j ∧ j ≤ 368)) → RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins)
    scope image loadBase base offS budget j (stateAt real e j)
  inv369 : RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base
    (fun _ => callerPC + 4#64 - base) budget 369 (stateAt real e 369)
  sp3 : (stateAt real e 3).regs.SP_EL0 = BitVec.ofNat 64 pins.sp
  sp365 : (stateAt real e 365).regs.SP_EL0 = BitVec.ofNat 64 pins.sp
  present365 : RtShim.SlotPrem.ShimSlotPresent pins mapping (stateAt real e 365)
  ditOn : ∀ j, 5 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1
  ditRestored : (stateAt real e 368).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧
    (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT
  x30_364 : (stateAt real e 364).regs.gpr[(GPRSummary.key (30#5).toNat).val] = base + offS 365
  x30_368 : (stateAt real e 368).regs.gpr[30] = callerPC + 4#64
  sp369 : (stateAt real e 369).regs.SP_EL0 = e.regs.SP_EL0
  x30_369 : (stateAt real e 369).regs.gpr[30] = e.regs.gpr[30]
  keepPre : ∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 → (stateAt real e 7).regs.gpr[i.val] = e.regs.gpr[i.val]
  keepPost : ∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 →
    (stateAt real e 369).regs.gpr[i.val] = (stateAt real e 364).regs.gpr[i.val]

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Release.shim_chain"
  (← IO.getStderr).flush

theorem shim_chain (real : Type) [Sail.SailReal real]
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
    (low365 : (base + offS 365).toNat < 2 ^ 55)
    (closed365 : ClosedMembershipAt spec config rows mapping (shimMap spec mapping base pins)
      (ArmBridge.CruxGenGuarded.beforeFetchState (stateAt real e 365)))
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
    ShimChain real spec config rows mapping pins scope image loadBase base offS budget e callerPC := by
  have I : ∀ j, (j ≤ 6 ∨ (365 ≤ j ∧ j ≤ 368)) → j < budget := fun j h => by omega
  have straight : ∀ j, (365 ≤ j ∧ j ≤ 367) → offS (j + 1) = offS j + 4#64 := by
    intro j ⟨a, b⟩
    rw [offPost (j + 1) (by omega) (by omega), offPost j a (by omega),
      show j + 1 - 358 = (j - 358) + 1 by omega, shimPC_succ]
  have nodup := dp.nodup
  have i7 := pre.inv7
  have link := pre.x30_7
  have x30_3 := pre.x30_3
  have sp3 := pre.sp3
  have slot4 := pre.slot4
  -- the body and its RET to s7
  have hE := e17_general real spec config rows mapping base pins (stateAt real e 7) bodyBudget dp (by omega)
  have inv357 := (hE.1 357 (by omega)).1
  have x30 : (stateAt real (stateAt real e 7) 357).regs.gpr[(GPRSummary.key (30#5).toNat).val] = base + offS 365 :=
    hE.2.trans link
  have hRes := HeapV2StepCerts.Residue.Run.residue_general real spec config rows mapping base pins (stateAt real e 7)
    bodyBudget dp (by omega)
  have bodyMem : ∀ a, ¬ Residue.StoreBytes pins mapping a →
      (stateAt real (stateAt real e 7) 357).mem[a]? = (stateAt real e 7).mem[a]? := (hRes 357 (by omega)).2.1.2
  have hCT := HeapV2StepCerts.Residue.Run.ct2Residue_run real spec config rows mapping base pins (stateAt real e 7)
    bodyBudget dp (by omega)
  have sp7 := pre.sp7
  have sp364 : (stateAt real (stateAt real e 7) 357).regs.SP_EL0 = BitVec.ofNat 64 pins.sp :=
    hCT.2.2.2.1.trans sp7
  have s364 : stateAt real e 364 = stateAt real (stateAt real e 7) 357 := stateAt_add real e 7 357
  have J364 := RtShim2.ShimBranch.shimInv_of_chainInv3 inv357.v3
  have fetch357 := MemNext.memFetch spec config rows mapping base bodyBudget 357 pins
    (rowsFootprint spec.imageRows).byte dp.static 0xc0 0xd65f03c0 (by decide +kernel) (by decide +kernel)
    (EntryBodyRet.W 30#5) (by decide) _ inv357.v3.v2
  obtain ⟨f, r364, i365, gR, spR, mR, _⟩ := RtShim2.ShimBranch.plan_shim_ret real spec config rows mapping _ _ _ _
    dp.static.separated base HeapV2Compose.offsetOf bodyBudget 357 (by omega) dp.page (by decide +kernel) 30#5
    (by decide) (by decide) _ J364 (by rw [x30]; exact low365) offS budget 365 hbudget x30 fetch357
  have e365 : stateAt real e 365 = f := by
    rw [show (365 : Nat) = 7 + 358 from rfl, stateAt_add real e 7 358]; exact stateAt_succ_of r364
  rw [← e365] at i365 spR mR gR
  rw [← s364] at r364
  have placed365 : MemReloc.ImageOn scope image (stateAt real e 365) loadBase mapping :=
    HeapV2StepCerts.placed_class mR (HeapV2StepCerts.placed_class_writes bodyMem codeStore i7.v2.placed)
  have J365 : RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins)
      scope image loadBase base offS budget 365 (stateAt real e 365) :=
    { v2 := ⟨i365.v2.v1, closed365, placed365, i365.v2.branch⟩, raw := i365.raw, noUpd := i365.noUpd,
      post2 := i365.post2, mode := i365.mode, debug := i365.debug, feat := i365.feat, dcache := i365.dcache }
  have sp365 : (stateAt real e 365).regs.SP_EL0 = BitVec.ofNat 64 pins.sp := by rw [spR, ← s364]; exact s364 ▸ sp364
  -- the slot from s3's STP to s7
  have keepBody : ∀ n, mapping (BitVec.ofNat 64 pins.sp) = some n → ∀ i < 16,
      (stateAt real e 365).mem[n + i]? = (stateAt real e 4).mem[n + i]? := by
    intro n hn i hi
    rw [mR]
    refine (bodyMem (n + i) (sep _ ⟨n, hn, by omega, by omega⟩)).trans ?_
    exact pre.mem47 _
  have slot365 : SlotHas pins mapping (ArmCertMem.StpEval.stpData (stateAt real e 3) 9#5 30#5) (stateAt real e 365) :=
    fun n hn i hi => (keepBody n hn i hi).trans (slot4 n hn i hi)
  have present365 : RtShim.SlotPrem.ShimSlotPresent pins mapping (stateAt real e 365) := fun n hn i hi => by
    rw [slot365 n hn i hi]; rfl
  -- epilogue chain
  have x30_366 := ev_succ (shim_ldp_hi real spec config rows mapping scope image loadBase base offS budget 365
    (I 365 (by omega)) page (aligned 365) _ J365 static sp365 spAligned present365 ob365)
  obtain ⟨f, r365, i366, h366, _, _, _⟩ := RtShim2.ShimMem.plan_shim_mem real spec config rows mapping _ pins scope
    image loadBase separated base offS budget 365 (I 365 (by omega)) page (aligned 365) _ codeSlot _ _ _ _
    (fun x => x.regs._PC + 4#64) _ J365 present365 sp365
    (RtShim2.ShimMem.memS_Ldp real spec config rows mapping static spAligned 9#5 30#5 (by decide) (by decide)
      (by decide) (by decide +kernel) _) (next_placed J365.v2.v1.pc (straight 365 ⟨by omega, by omega⟩)) ob365
  have e366 : stateAt real e 366 = f := stateAt_succ_of r365
  rw [← e366] at i366 h366 r365
  obtain ⟨f, r366, i367, h367, _, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 366 (I 366 (by omega)) page (aligned 366) _ _ _ _ (fun x => x.regs._PC + 4#64) _
    i366 (classE_toV tail8) (next_placed i366.v2.v1.pc (straight 366 ⟨by omega, by omega⟩)) ob8
  have e367 : stateAt real e 367 = f := stateAt_succ_of r366
  rw [← e367] at i367 h367 r366
  obtain ⟨f, r367, i368, h368, _, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 367 (I 367 (by omega)) page (aligned 367) _ _ _ _ (fun x => x.regs._PC + 4#64) _
    i367 (NativeShimTails.msrDit9_tailVAt real _ prof9) (next_placed i367.v2.v1.pc (straight 367 ⟨by omega, by omega⟩)) ob9
  have e368 : stateAt real e 368 = f := stateAt_succ_of r367
  rw [← e368] at i368 h368 r367
  have x30_368 : (stateAt real e 368).regs.gpr[30] = callerPC + 4#64 := by
    rw [RtSaved.kept_reg h368 ⟨30, by decide⟩ rfl, RtSaved.kept_reg h367 ⟨30, by decide⟩ (keep8all _),
      x30_366 _ slot365, ldpHi_stpData, x30_3, callerX30]
  have tgt : (stateAt real e 368).regs.gpr[(GPRSummary.key (30#5).toNat).val] =
      base + (fun _ => callerPC + 4#64 - base) 369 := by
    show (stateAt real e 368).regs.gpr[30] = _
    rw [x30_368]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub]
    omega
  obtain ⟨f, r368, i369, g369, sp369, _, _⟩ := RtShim2.ShimBranch.plan_shim_ret real spec config rows mapping _
    scope image loadBase separated base offS budget 368 (I 368 (by omega)) page (aligned 368) 30#5 (by decide)
    (by decide) _ i368
    (by show ((stateAt real e 368).regs.gpr[30]).toNat < _; rw [x30_368]; exact low10) (fun _ => callerPC + 4#64 - base) budget 369 rfl tgt ob10
  have e369 : stateAt real e 369 = f := stateAt_succ_of r368
  rw [← e369] at i369 g369 sp369 r368
  -- SP through the epilogue
  have sp366 : (stateAt real e 366).regs.SP_EL0 = (stateAt real e 365).regs.SP_EL0 := h366 .sp
  have sp367 : (stateAt real e 367).regs.SP_EL0 = (stateAt real e 366).regs.SP_EL0 + BitVec.ofInt 64 16 := by
    have h := h367 .sp; rw [add8] at h; exact h
  have sp369' : (stateAt real e 369).regs.SP_EL0 = e.regs.SP_EL0 := by
    have k368 : (stateAt real e 368).regs.SP_EL0 = (stateAt real e 367).regs.SP_EL0 := h368 .sp
    rw [sp369, k368, sp367, sp366, sp365, spE]
  -- the DIT window (body facts: dit_body_mem / dit_body_ret for DIT, the residue's StoreBytes frame for the slot)
  have hbody : ∀ j, 7 ≤ j → j ≤ 365 → (stateAt real e j).regs.PSTATE.DIT = (stateAt real e 7).regs.PSTATE.DIT ∧
      SlotKeep pins mapping (stateAt real e 7) (stateAt real e j) := by
    intro j lo hi
    obtain ⟨k, rfl⟩ : ∃ k, j = 7 + k := ⟨j - 7, by omega⟩
    rcases Nat.lt_or_ge k 358 with h | h
    · rw [stateAt_add real e 7 k]
      refine ⟨(dit_body_mem real spec config rows mapping base pins (stateAt real e 7) bodyBudget dp (by omega) k
        (by omega)).1, fun n hn i hi => ?_⟩
      exact (hRes k (by omega)).2.1.2 (n + i) (sep _ ⟨n, hn, by omega, by omega⟩)
    · obtain rfl : k = 358 := by omega
      refine ⟨?_, fun n hn i hi => ?_⟩
      · rw [stateAt_add real e 7 358]
        exact (dit_body_ret real spec config rows mapping base pins (stateAt real e 7) bodyBudget dp hbB
          (by rw [x30]; exact low365)).1
      · show (stateAt real e 365).mem[n + i]? = _
        rw [mR]
        exact bodyMem (n + i) (sep _ ⟨n, hn, by omega, by omega⟩)
  have invAll : ∀ j, (j ≤ 6 ∨ (365 ≤ j ∧ j ≤ 368)) →
      RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins)
        scope image loadBase base offS budget j (stateAt real e j) := by
    intro j hj
    by_cases h6 : j ≤ 6
    · exact pre.inv j h6
    rcases (show j = 365 ∨ j = 366 ∨ j = 367 ∨ j = 368 by omega) with rfl | rfl | rfl | rfl
    · exact J365
    · exact i366
    · exact i367
    · exact i368
  have win := dit_window_shim real spec config rows mapping scope image loadBase base offS budget e room page aligned
    invAll ob0 (classE_toV tail1) hw1 ob1 prof2 ob2 static spAligned sp3 ob3 prof4 ob4 prof5 ob5 imm26 controls6
    (by rw [bl7]; exact low6) ob6 hbody sp365 present365 ob365 (classE_toV tail8) hw8 (keep8all _) ob8 prof9 ob9
    (by decide +kernel) (by show ((stateAt real e 368).regs.gpr[30]).toNat < _; rw [x30_368]; exact low10) ob10
  have kLdp : ∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 → RegBind.updOf (RegBind.updLdp 9#5 30#5) (.x i) = .keep := by
    decide
  refine
    { runs := fun j hj => ?_, inv := invAll, inv369 := i369, sp3 := sp3, sp365 := sp365, present365 := present365,
      ditOn := win.1, ditRestored := win.2, x30_364 := s364 ▸ x30, x30_368 := x30_368, sp369 := sp369',
      x30_369 := ?_, keepPre := pre.keepPre, keepPost := ?_ }
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 364 ∨ j = 365 ∨ j = 366 ∨ j = 367 ∨
      j = 368 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pre.runs 0 (by omega)
    · exact pre.runs 1 (by omega)
    · exact pre.runs 2 (by omega)
    · exact pre.runs 3 (by omega)
    · exact pre.runs 4 (by omega)
    · exact pre.runs 5 (by omega)
    · exact pre.runs 6 (by omega)
    · rw [← e365] at r364; exact r364
    · exact r365
    · exact r366
    · exact r367
    · exact r368
  · show (stateAt real e 369).regs.gpr[30] = _
    rw [g369, x30_368, callerX30]
  · intro i n9 n30
    rw [g369, RtSaved.kept_reg h368 i rfl, RtSaved.kept_reg h367 i (keep8all i), RtSaved.kept_reg h366 i (kLdp i n9 n30),
      gR, s364]

#print axioms shim_chain
end RtDit.Release
