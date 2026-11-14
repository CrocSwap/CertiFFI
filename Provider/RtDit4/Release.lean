-- (H-P13 → certiffi's release headline, e4953b32 + shimData fix): Release.ShimPrologue and
-- Release.ShimEpilogue from the actual shim run. shim_release establishes, along stateAt e: the shim's ShimInv
-- chain (plan_shim_*), the body under e17_general at σ 7 (DeploymentPremises premise: bodyPremises_of),
-- the body's final RET back to s7 (call/return; X30 = the BL link), the epilogue, and the caller return at 369
-- (s10 RET to X30 = e's X30 = callerPC + 4, the caller contract). Fields: steps, E17 (shimMap) at shim states and
-- 369, EvShape per shim step and the body RET (RtDit.ShimEv), PCs (offS = shimPC), DIT window/restoration,
-- SP/X30 frame (slot round trip), qBody (X2/X3 kept), ditBody.
import RtDit4.ShimEv2
import RtDit3.ShimRun
import Bridge.CruxGenGuarded.ReleaseHeadline
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

theorem shimPC_succ (j : Nat) : shimPC (j + 1) = shimPC j + 4#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [shimPC, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- LDP X9, X30: X30 := the high half of the slot's 16 bytes. -/
theorem shim_ldp_hi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {pbase : Nat} {table : Nat → Prop}
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (x : NativeState)
    (inv : RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
      scope image loadBase base offset budget k x)
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (spX : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp) (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (present : RtShim.SlotPrem.ShimSlotPresent p mapping x)
    (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ∀ d : BitVec 128, SlotHas p mapping d x → fin.regs.gpr[30] = ArmCertMem.LdpEval.ldpHi d := by
  obtain ⟨final, fin, run, _, mF, _, _, hi⟩ :=
    shim_gen real spec config rows mapping _ scope image loadBase base offset budget k room page aligned _ x inv ob
      (fun final fin => ∀ d : BitVec 128, SlotHas p mapping d final → fin.regs.gpr[30] = ArmCertMem.LdpEval.ldpHi d)
      (fun final enc0 f => by
        obtain ⟨acc, nx, hregs⟩ := f.regs
        have sysF : SysEq2 x.regs final.regs := EntryBranchPins.sysEq2_symm _ _ f.input.sys
        have spF : final.regs.SP_EL0 = BitVec.ofNat 64 p.sp := by
          rw [hregs, ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ x (fun _ _ => rfl)
            (fun _ => rfl) rfl]
          exact spX
        have post2F := HeapV2StepCerts.MemConfigFrame.post2 sysF.feat sysF.el sysF.nrw sysF.scr sysF.hcr sysF.sctlr sysF.spe inv.post2
        have modeF := HeapV2StepCerts.MemConfigFrame.mode sysF.feat sysF.el sysF.scr sysF.hcr inv.mode
        have debugF := HeapV2StepCerts.MemConfigFrame.debug sysF.mdscr sysF.hde inv.debug
        have featF : final.regs.FeatureImpl[7] = true ∧ final.regs.FeatureImpl[3] = false ∧
            final.regs.FeatureImpl[227] = false ∧ final.regs.FeatureImpl[111] = true := by
          rw [sysF.feat]; exact inv.feat
        have dcacheF := HeapV2StepCerts.MemConfigFrame.dcache sysF.sctlr inv.dcache
        have hva : ArmCertMem.LdpEval.ldpAddr final 0#7 = BitVec.ofNat 64 p.sp :=
          (RtShim.SlotPrem.shim_addr final).trans spF
        have presentF : RtShim.SlotPrem.ShimSlotPresent p mapping final := fun n hn i hi => by
          rw [f.mem]; exact present n hn i hi
        obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
          RtShim.SlotPrem.prem_shimLdp final f.closed static presentF spF spAligned
        obtain ⟨_, _, fin, _, _, _, run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hiF, _⟩ :=
          RtSaved3.MemTailP2.mem_tailP2_Ldp real spec config rows mapping x final enc0 0#7 9#5 30#5 (by decide)
            (by decide) (by decide) (by decide +kernel) f.pins f.input f.guard _ f.quiet f.it f.ss f.current perAcc
            modeF debugF post2F featF.1 featF.2.1 featF.2.2.1 featF.2.2.2 dcacheF hsp hal pa mapped mmio data bytes
            (fun _ => False) (by rw [f.mem]; exact inv.raw)
            (fun acc sh => by rw [hostHAFT_eq sysF]; exact inv.noUpd false acc sh)
        refine ⟨fin, run, ?_⟩
        intro d hd
        have hn : mapping (BitVec.ofNat 64 p.sp) = some pa.toNat := by rw [← hva]; exact mapped
        have same : data = d := RtSaved.bytes_ext (fun i hi =>
          Option.some.inj ((bytes i hi).symm.trans (hd pa.toNat hn i hi)))
        rw [← same]; exact hiF)
  exact ⟨fin, run, fun d hd => hi d (fun n hn i hi => by rw [mF]; exact hd n hn i hi)⟩

theorem ldpHi_stpData (s : NativeState) :
    ArmCertMem.LdpEval.ldpHi (ArmCertMem.StpEval.stpData s 9#5 30#5) = s.regs.gpr[30] := by
  unfold ArmCertMem.StpEval.stpData
  exact RtSaved.ldpHi_append _ _

theorem classE_toV {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes}
    {K : Int} {source : NativeState} {next : BitVec 64} {us : List (RegBind.Reg × RegBind.Upd)}
    (h : RegValE.ClassTailVAt real w writes K source next us) : RegVal.ClassTailVAt real w writes K source next us := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, run, frame, q, fp, sys, mem, gic, pc, np, _, _, holds⟩ :=
    h fetched enc0 budget pins input guard quiet it ss
  exact ⟨sp, a, fin, hook, run, frame, q, fp, sys, mem, gic, pc, np, holds⟩

theorem ev_succ {real : Type} [Sail.SailReal real] {e : NativeState} {j : Nat} {P : NativeState → Prop}
    (h : ∃ fin, modelStep real (stateAt real e j) = .ok () fin ∧ P fin) : P (stateAt real e (j + 1)) := by
  obtain ⟨fin, r, hp⟩ := h
  rw [stateAt_succ_of r]; exact hp

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Release.shim_release"
  (← IO.getStderr).flush

theorem shim_release (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (codeSlot : ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (codeData : ImageTableSeparated scope loadBase mapping (MemNext.dataBytes pins mapping))
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
    (sep : ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → ¬ MemNext.dataBytes pins mapping a)
    (ob0 : FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word (stateAt real e 0))
    {w1 : BitVec 32} {writes1 : NativeEntry.Effects.Writes} {K1 : Int} {us1 : List (RegBind.Reg × RegBind.Upd)}
    (tail1 : RegValE.ClassTailVAt real w1 writes1 K1 (stateAt real e 1) ((stateAt real e 1).regs._PC + 4#64) us1)
    (hw1 : writes1.dit = false) (sub1 : RegBind.updOf us1 .sp = .set .sp (-16))
    (keep1 : RegBind.updOf us1 (.x 2) = .keep ∧ RegBind.updOf us1 (.x 3) = .keep ∧ RegBind.updOf us1 (.x 30) = .keep)
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
    (sp364 : (stateAt real (stateAt real e 7) 357).regs.SP_EL0 = BitVec.ofNat 64 pins.sp)
    (closed365 : ClosedMembershipAt spec config rows mapping (shimMap spec mapping base pins)
      (ArmBridge.CruxGenGuarded.beforeFetchState (stateAt real e 365)))
    (ob365 : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7)
      (stateAt real e 365))
    {w8 : BitVec 32} {writes8 : NativeEntry.Effects.Writes} {K8 : Int} {us8 : List (RegBind.Reg × RegBind.Upd)}
    (tail8 : RegValE.ClassTailVAt real w8 writes8 K8 (stateAt real e 366) ((stateAt real e 366).regs._PC + 4#64) us8)
    (hw8 : writes8.dit = false) (add8 : RegBind.updOf us8 .sp = .set .sp 16)
    (keep8 : RegBind.updOf us8 (.x 9) = .keep ∧ RegBind.updOf us8 (.x 30) = .keep)
    (ob8 : FetchObligations spec config rows mapping w8 (stateAt real e 366))
    (prof9 : NativeEntryAdapters.MsrDit.Profile (stateAt real e 367))
    (ob9 : FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) (stateAt real e 367))
    (low10 : (callerPC + 4#64).toNat < 2 ^ 55)
    (ob10 : FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) (stateAt real e 368)) :
    ShimPrologue real spec config rows mapping base pins bodyBudget e ∧
      ShimEpilogue real spec mapping base pins callerPC e := by
  have I : ∀ j, (j ≤ 6 ∨ (365 ≤ j ∧ j ≤ 368)) → j < budget := fun j h => by omega
  have straight : ∀ j, (j ≤ 5 ∨ (365 ≤ j ∧ j ≤ 367)) → offS (j + 1) = offS j + 4#64 := by
    intro j h
    rcases h with h | ⟨a, b⟩
    · rw [offPre (j + 1) (by omega), offPre j (by omega), shimPC_succ]
    · rw [offPost (j + 1) (by omega) (by omega), offPost j a (by omega),
        show j + 1 - 358 = (j - 358) + 1 by omega, shimPC_succ]
  have ret365 : offS 365 = offS 6 + 4#64 := by
    rw [offPost 365 (by omega) (by omega), offPre 6 (by omega)]; exact shimPC_succ 6
  have nodup := dp.nodup
  have N : ∀ x : NativeState, x.regs._PC + 4#64 = x.regs._PC + 4#64 := fun _ => rfl
  -- prologue chain
  obtain ⟨f, r, i1, h1, m1, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 0 (I 0 (by omega)) page (aligned 0) _ _ _ _ (fun x => x.regs._PC + 4#64) e inv0
    (NativeShimTails.btiC_tailVAt real e) (next_placed inv0.v2.v1.pc (straight 0 (by omega))) ob0
  have e1 : stateAt real e 1 = f := stateAt_succ_of r
  rw [← e1] at i1 h1 m1 r
  obtain ⟨f, r1, i2, h2, m2, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 1 (I 1 (by omega)) page (aligned 1) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i1
    (classE_toV tail1) (next_placed i1.v2.v1.pc (straight 1 (by omega))) ob1
  have e2 : stateAt real e 2 = f := stateAt_succ_of r1
  rw [← e2] at i2 h2 m2 r1
  obtain ⟨f, r2, i3, h3, m3, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 2 (I 2 (by omega)) page (aligned 2) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i2
    (NativeShimTails.mrsDit9_tailVAt real _ prof2) (next_placed i2.v2.v1.pc (straight 2 (by omega))) ob2
  have e3 : stateAt real e 3 = f := stateAt_succ_of r2
  rw [← e3] at i3 h3 m3 r2
  have k9 : ∀ i : Fin 31, i.val ≠ 9 → RegBind.updOf [(RegBind.Reg.x 9, RegBind.Upd.drop)] (.x i) = .keep := by
    intro i hi
    simp only [RegBind.updOf, List.find?]
    have : (RegBind.Reg.x 9 = RegBind.Reg.x i) = False := by
      simp only [RegBind.Reg.x.injEq, eq_iff_iff, iff_false]; intro h; exact hi (by rw [← h]; rfl)
    simp [this]
  have sp1 : (stateAt real e 1).regs.SP_EL0 = e.regs.SP_EL0 := h1 .sp
  have sp2 : (stateAt real e 2).regs.SP_EL0 = (stateAt real e 1).regs.SP_EL0 + BitVec.ofInt 64 (-16) := by
    have h := h2 .sp; rw [sub1] at h; exact h
  have z16 : BitVec.ofInt 64 16 + BitVec.ofInt 64 (-16) = 0#64 := by decide
  have sp3 : (stateAt real e 3).regs.SP_EL0 = BitVec.ofNat 64 pins.sp := by
    have h : (stateAt real e 3).regs.SP_EL0 = (stateAt real e 2).regs.SP_EL0 := h3 .sp
    rw [h, sp2, sp1, spE, BitVec.add_assoc, z16, BitVec.add_zero]
  have slot3 : RtShim.SlotPrem.ShimSlotPresent pins mapping (stateAt real e 3) := fun n hn i hi => by
    rw [m3, m2, m1]; exact slotE n hn i hi
  obtain ⟨f, r3, i4, h4, _, k4, _⟩ := RtShim2.ShimMem.plan_shim_mem real spec config rows mapping _ pins scope image
    loadBase separated base offS budget 3 (I 3 (by omega)) page (aligned 3) _ codeSlot _ _ _ _
    (fun x => x.regs._PC + 4#64) _ i3 slot3 sp3
    (RtShim2.ShimMem.memS_Stp real spec config rows mapping static spAligned 9#5 30#5 (by decide) (by decide)
      (by decide +kernel) _) (next_placed i3.v2.v1.pc (straight 3 (by omega))) ob3
  have e4 : stateAt real e 4 = f := stateAt_succ_of r3
  rw [← e4] at i4 h4 k4 r3
  obtain ⟨f, r4, i5, h5, m5, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 4 (I 4 (by omega)) page (aligned 4) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i4
    (NativeShimTails.ditOn_tailVAt real _ prof4) (next_placed i4.v2.v1.pc (straight 4 (by omega))) ob4
  have e5 : stateAt real e 5 = f := stateAt_succ_of r4
  rw [← e5] at i5 h5 m5 r4
  obtain ⟨f, r5, i6, h6, m6, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 5 (I 5 (by omega)) page (aligned 5) _ _ _ _ (fun x => x.regs._PC + 4#64) _ i5
    (NativeShimTails.isbSy_tailVAt real _ prof5) (next_placed i5.v2.v1.pc (straight 5 (by omega))) ob5
  have e6 : stateAt real e 6 = f := stateAt_succ_of r5
  rw [← e6] at i6 h6 m6 r5
  obtain ⟨f, r6, i7, g7, _, m7, _⟩ := RtShim2.ShimBranch.plan_shim_bl real spec config rows mapping _ scope image
    loadBase separated base offS budget 6 (I 6 (by omega)) page (aligned 6) nodup imm26 _ i6
    (by rw [bl7]; exact low6) controls6 offS budget 7 rfl bl7 ob6
  have e7 : stateAt real e 7 = f := stateAt_succ_of r6
  rw [← e7] at i7 g7 m7 r6
  -- X2/X3/X30 through the prologue
  have keepReg : ∀ i : Fin 31, (i = 2 ∨ i = 3) →
      (stateAt real e 7).regs.gpr[i.val] = e.regs.gpr[i.val] := by
    intro i hi
    have n9 : i.val ≠ 9 := by rcases hi with rfl | rfl <;> decide
    have n30 : i.val ≠ 30 := by rcases hi with rfl | rfl <;> decide
    have u1 : RegBind.updOf us1 (.x i) = .keep := by rcases hi with rfl | rfl; exact keep1.1; exact keep1.2.1
    rw [g7, Vector.getElem_set_ne _ _ (by omega), RtSaved.kept_reg h6 i rfl, RtSaved.kept_reg h5 i rfl,
      RtSaved.kept_reg h4 i rfl, RtSaved.kept_reg h3 i (k9 i n9), RtSaved.kept_reg h2 i u1, RtSaved.kept_reg h1 i rfl]
  have x30_3 : (stateAt real e 3).regs.gpr[30] = e.regs.gpr[30] := by
    rw [RtSaved.kept_reg h3 ⟨30, by decide⟩ (k9 _ (by decide)), RtSaved.kept_reg h2 ⟨30, by decide⟩ keep1.2.2,
      RtSaved.kept_reg h1 ⟨30, by decide⟩ rfl]
  have link : (stateAt real e 7).regs.gpr[30] = base + offS 365 := by
    rw [g7, Vector.getElem_set_self, i6.v2.v1.pc, ret365, BitVec.add_assoc]
  -- the body and its RET to s7
  have hE := e17_general real spec config rows mapping base pins (stateAt real e 7) bodyBudget dp (by omega)
  have inv357 := (hE.1 357 (by omega)).1
  have x30 : (stateAt real (stateAt real e 7) 357).regs.gpr[(GPRSummary.key (30#5).toNat).val] = base + offS 365 :=
    hE.2.trans link
  have bodyMem := (dit_body_mem real spec config rows mapping base pins (stateAt real e 7) bodyBudget dp (by omega)
    357 (by omega)).2
  have s364 : stateAt real e 364 = stateAt real (stateAt real e 7) 357 := stateAt_add real e 7 357
  have J364 := RtShim2.ShimBranch.shimInv_of_chainInv3 inv357.v3
  have fetch357 := MemNext.memFetch spec config rows mapping base bodyBudget 357 pins
    (rowsFootprint spec.imageRows).byte dp.static 0xc0 0xd65f03c0 (by decide +kernel) (by decide +kernel)
    (EntryBodyRet.W 30#5) (by decide) _ inv357.v3.v2
  obtain ⟨f, r364, i365, _, spR, mR, _⟩ := RtShim2.ShimBranch.plan_shim_ret real spec config rows mapping _ _ _ _
    dp.static.separated base HeapV2Compose.offsetOf bodyBudget 357 (by omega) dp.page (by decide +kernel) 30#5
    (by decide) (by decide) _ J364 (by rw [x30]; exact low365) offS budget 365 hbudget x30 fetch357
  have e365 : stateAt real e 365 = f := by
    rw [show (365 : Nat) = 7 + 358 from rfl, stateAt_add real e 7 358]; exact stateAt_succ_of r364
  rw [← e365] at i365 spR mR
  rw [← s364] at r364
  have placed365 : MemReloc.ImageOn scope image (stateAt real e 365) loadBase mapping :=
    HeapV2StepCerts.placed_class mR (HeapV2StepCerts.placed_class_writes bodyMem codeData i7.v2.placed)
  have J365 : RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins)
      scope image loadBase base offS budget 365 (stateAt real e 365) :=
    { v2 := ⟨i365.v2.v1, closed365, placed365, i365.v2.branch⟩, raw := i365.raw, noUpd := i365.noUpd,
      post2 := i365.post2, mode := i365.mode, debug := i365.debug, feat := i365.feat, dcache := i365.dcache }
  have sp365 : (stateAt real e 365).regs.SP_EL0 = BitVec.ofNat 64 pins.sp := by rw [spR, ← s364]; exact s364 ▸ sp364
  -- the slot from s3's STP to s7
  obtain ⟨fS, rS, _, slot4, _⟩ := shim_stp real spec config rows mapping scope image loadBase base offS budget 3
    (I 3 (by omega)) page (aligned 3) _ i3 static sp3 spAligned ob3
  have eS : stateAt real e 4 = fS := stateAt_succ_of rS
  rw [← eS] at slot4
  have keepBody : ∀ n, mapping (BitVec.ofNat 64 pins.sp) = some n → ∀ i < 16,
      (stateAt real e 365).mem[n + i]? = (stateAt real e 4).mem[n + i]? := by
    intro n hn i hi
    rw [mR]
    refine (bodyMem (n + i) (sep _ ⟨n, hn, by omega, by omega⟩)).trans ?_
    rw [m7, m6, m5]
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
      (by decide) (by decide +kernel) _) (next_placed J365.v2.v1.pc (straight 365 (by omega))) ob365
  have e366 : stateAt real e 366 = f := stateAt_succ_of r365
  rw [← e366] at i366 h366 r365
  obtain ⟨f, r366, i367, h367, _, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 366 (I 366 (by omega)) page (aligned 366) _ _ _ _ (fun x => x.regs._PC + 4#64) _
    i366 (classE_toV tail8) (next_placed i366.v2.v1.pc (straight 366 (by omega))) ob8
  have e367 : stateAt real e 367 = f := stateAt_succ_of r366
  rw [← e367] at i367 h367 r366
  obtain ⟨f, r367, i368, h368, _, _⟩ := RtShim2.plan_shim_class real spec config rows mapping _ scope image loadBase
    separated base offS budget 367 (I 367 (by omega)) page (aligned 367) _ _ _ _ (fun x => x.regs._PC + 4#64) _
    i367 (NativeShimTails.msrDit9_tailVAt real _ prof9) (next_placed i367.v2.v1.pc (straight 367 (by omega))) ob9
  have e368 : stateAt real e 368 = f := stateAt_succ_of r367
  rw [← e368] at i368 h368 r367
  have x30_368 : (stateAt real e 368).regs.gpr[30] = callerPC + 4#64 := by
    rw [RtSaved.kept_reg h368 ⟨30, by decide⟩ rfl, RtSaved.kept_reg h367 ⟨30, by decide⟩ keep8.2,
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
  -- the DIT window
  have win := dit_shim_run real spec config rows mapping scope image loadBase separated codeSlot codeData base offS
    budget e room page aligned straight ret365 inv0 slotE
    (by rw [spE, BitVec.add_assoc, z16, BitVec.add_zero]) static spAligned sep ob0 (classE_toV tail1) hw1 sub1 ob1
    prof2 ob2 ob3 prof4 ob4 prof5 ob5 imm26 controls6 bl7 low6 ob6 bodyBudget dp hbB hbudget low365 sp364 closed365
    ob365 (classE_toV tail8) hw8 keep8.1 ob8 prof9 ob9
    (by show ((stateAt real e 368).regs.gpr[30]).toNat < _; rw [x30_368]; exact low10) ob10
  -- E17
  -- event shapes
  have pcPre : ∀ j, j ≤ 6 → offS j = shimPC j := offPre
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun e' he' => he' ▸ dp, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- ShimPrologue.steps
  · intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
  -- e17
  · intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact e17_of_shimInv agrees inv0
    · exact e17_of_shimInv agrees i1
    · exact e17_of_shimInv agrees i2
    · exact e17_of_shimInv agrees i3
    · exact e17_of_shimInv agrees i4
    · exact e17_of_shimInv agrees i5
    · exact e17_of_shimInv agrees i6
  -- ev
  · intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 0 (I 0 (by omega))
        page (aligned 0) nodup _ _ inv0 ob0 _ tail_btiC)
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 1 (I 1 (by omega))
        page (aligned 1) nodup _ _ i1 ob1 _ (tail_classE tail1))
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 2 (I 2 (by omega))
        page (aligned 2) nodup _ _ i2 ob2 _ (tail_mrs9 prof2))
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 3 (I 3 (by omega))
        page (aligned 3) nodup _ _ i3 ob3 _ (tail_stpE i3 static sp3 spAligned nodup))
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 4 (I 4 (by omega))
        page (aligned 4) nodup _ _ i4 ob4 _ (tail_ditOn prof4))
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 5 (I 5 (by omega))
        page (aligned 5) nodup _ _ i5 ob5 _ (tail_isb prof5))
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 6 (I 6 (by omega))
        page (aligned 6) nodup _ _ i6 ob6 _ (tail_bl imm26 controls6 (by rw [bl7]; exact low6)))
  -- pc
  · intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show e.regs._PC = _; rw [inv0.v2.v1.pc, offPre 0 (by omega)]
    · rw [i1.v2.v1.pc, offPre 1 (by omega)]
    · rw [i2.v2.v1.pc, offPre 2 (by omega)]
    · rw [i3.v2.v1.pc, offPre 3 (by omega)]
    · rw [i4.v2.v1.pc, offPre 4 (by omega)]
    · rw [i5.v2.v1.pc, offPre 5 (by omega)]
    · rw [i6.v2.v1.pc, offPre 6 (by omega)]
  -- ditOn
  · intro j a b; exact win.1 j a (by omega)
  -- qBody
  · show HeapV2StepCerts.E17General.qOf (stateAt real e 7) = HeapV2StepCerts.E17General.qOf e
    unfold HeapV2StepCerts.E17General.qOf
    simp only [RegBind.regVal]
    rw [keepReg 2 (Or.inl rfl), keepReg 3 (Or.inr rfl)]
  -- ditBody
  · exact win.1 7 (by omega) (by omega)
  -- ShimEpilogue.steps
  · intro j a b
    rcases (show j = 364 ∨ j = 365 ∨ j = 366 ∨ j = 367 ∨ j = 368 by omega) with rfl | rfl | rfl | rfl | rfl
    · rw [← e365] at r364; exact r364
    · exact r365
    · exact r366
    · exact r367
    · exact r368
  -- e17
  · intro j a b
    rcases (show j = 365 ∨ j = 366 ∨ j = 367 ∨ j = 368 ∨ j = 369 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact e17_of_shimInv agrees J365
    · exact e17_of_shimInv agrees i366
    · exact e17_of_shimInv agrees i367
    · exact e17_of_shimInv agrees i368
    · exact e17_of_shimInv agrees i369
  -- evRet: the body's final RET
  · have hq := ev_succ (j := 364) (e := e) (shim_ev real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf
      bodyBudget 357 (by omega) dp.page (by decide +kernel) nodup _ _ (s364 ▸ J364) (s364 ▸ fetch357) _
      (tail_ret 30#5 (by decide) (by decide) (s364 ▸ J364).v2.v1.pins (s364 ▸ J364).v2.branch
        (by rw [s364, x30]; exact low365)))
    exact hq
  -- ev 365..368
  · intro j a b
    rcases (show j = 365 ∨ j = 366 ∨ j = 367 ∨ j = 368 by omega) with rfl | rfl | rfl | rfl
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 365
        (I 365 (by omega)) page (aligned 365) nodup _ _ J365 ob365 _ (tail_ldpE J365 static present365 sp365 spAligned nodup))
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 366
        (I 366 (by omega)) page (aligned 366) nodup _ _ i366 ob8 _ (tail_classE tail8))
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 367
        (I 367 (by omega)) page (aligned 367) nodup _ _ i367 ob9 _ (tail_msr9 prof9))
    · exact ev_succ (shim_ev real spec config rows mapping _ scope image loadBase base offS budget 368
        (I 368 (by omega)) page (aligned 368) nodup _ _ i368 ob10 _
        (tail_ret 30#5 (by decide) (by decide) i368.v2.v1.pins i368.v2.branch
          (by show ((stateAt real e 368).regs.gpr[30]).toNat < _; rw [x30_368]; exact low10)))
  -- pc 365..368
  · intro j a b
    rcases (show j = 365 ∨ j = 366 ∨ j = 367 ∨ j = 368 by omega) with rfl | rfl | rfl | rfl
    · rw [J365.v2.v1.pc, offPost 365 (by omega) (by omega)]
    · rw [i366.v2.v1.pc, offPost 366 (by omega) (by omega)]
    · rw [i367.v2.v1.pc, offPost 367 (by omega) (by omega)]
    · rw [i368.v2.v1.pc, offPost 368 (by omega) (by omega)]
  -- exitPC
  · rw [i369.v2.v1.pc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub]
    omega
  -- ditOn 365..367
  · intro j a b; exact win.1 j (by omega) b
  -- ditRestored
  · exact ⟨win.2.1, win.2.2⟩
  -- frame
  · refine ⟨sp369', ?_⟩
    show (stateAt real e 369).regs.gpr[30] = _
    rw [g369, x30_368, callerX30]

#print axioms shim_release
end RtDit.Release
