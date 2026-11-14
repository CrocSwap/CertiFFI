-- split of shim_release_v2, part C = shim_keep (Release.ShimKeep: frameRegs/X19/_Z across s0..s6 and 364..368).
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
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
open NativeEntryCallerParts ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ClosedChain
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option Elab.async false
namespace RtDit.Release
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts
open ArmBridge.CruxGenGuarded.Release (shimPC shimData shimMap ShimPrologue ShimEpilogue)


theorem e20_z (fetched sp : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp) :
    sp.regs._Z = fetched.regs._Z :=
  frame_pres_E20 (fun x => x._Z) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne])
    (entry_spec_post fetched sp (budget + 1) quiet hook).frame

theorem frame_z {writes : NativeEntry.Effects.Writes} {t u : NativeState}
    (h : NativeEntryContract.Frame writes t u) (hv : writes.vector = false) : u.regs._Z = t.regs._Z := by
  have e := congrArg (fun r : Regs => r._Z) h.nonProj
  simpa [NativeEntry.Effects.mask, NativeEntry.Effects.erase, ArmCertCT.CT2.mask, hv] using e

theorem np_z {r r' : Regs} (h : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap r r') : r'._Z = r._Z := by
  have e := congrArg (fun q : Regs => q._Z) h
  simpa [ArmCertCT.CT2.mask] using e

theorem tail_z (fetched sp a fin : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    {writes : NativeEntry.Effects.Writes} (w : BitVec 32) (K : Int)
    (frame : NativeEntryContract.Frame writes (actionState w sp K) a) (hv : writes.vector = false)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    fin.regs._Z = fetched.regs._Z :=
  (np_z np).trans ((frame_z frame hv).trans (e20_z fetched sp budget quiet hook))

/-- A shim step whose tail keeps _Z keeps _Z (the fetch keeps it). -/
theorem shim_z (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (x : NativeState)
    (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
    (ob : FetchObligations spec config rows mapping w x)
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping m x final (budget - (k + 1)) →
      ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ fin.regs._Z = final.regs._Z) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z := by
  obtain ⟨final, fin, run, _, _, _, _, z, zf⟩ :=
    shim_gen real spec config rows mapping m scope image loadBase base offset budget k room page aligned w x inv ob
      (fun final fin => fin.regs._Z = final.regs._Z ∧ final.regs._Z = x.regs._Z)
      (fun final enc0 f => by
        obtain ⟨fin, run, z⟩ := tail final enc0 f
        obtain ⟨acc, nx, hregs⟩ := f.regs
        refine ⟨fin, run, z, ?_⟩
        rw [hregs]
        exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r._Z) _ _ x (fun _ _ => rfl)
          (fun _ => rfl) rfl)
  exact ⟨fin, run, z.trans zf⟩

section
variable {real : Type} [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {x : NativeState}

theorem z_class {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)} (tail : RegVal.ClassTailVAt real w writes K x next us)
    (hv : writes.vector = false) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ fin.regs._Z = final.regs._Z := by
  intro final enc0 f
  obtain ⟨sp, a, fin, hook, run, frame, _, _, _, _, _, _, np, _⟩ :=
    tail final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss
  exact ⟨fin, run, tail_z final sp a fin budget f.quiet hook w K frame hv np⟩

theorem z_classE {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)} (tail : RegValE.ClassTailVAt real w writes K x next us) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ fin.regs._Z = final.regs._Z := by
  intro final enc0 f
  obtain ⟨_, _, fin, _, run, _, _, _, _, _, _, _, _, _, z, _⟩ :=
    tail final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss
  exact ⟨fin, run, z⟩

theorem z_ret (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (stepPins : StepPins x) (bp : Crypto.BranchV2.BranchPinsV2PA x)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x (EntryBodyRet.W Rn) enc0 final = .ok () fin ∧ fin.regs._Z = final.regs._Z := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have bpF := EntryFetchedBranch.fetched_branch_pins acc nx x final stepPins hregs bp
  obtain ⟨_, _, fin, _, run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, z⟩ :=
    EntryBodyRet.native_tail_z real x final enc0 Rn hRn noEret f.pins bpF f.input f.guard budget f.quiet f.it f.ss hlow
  exact ⟨fin, run, z⟩

theorem z_bl (imm26 : BitVec 26) (controls : CallerControls x) (low : (blTarget imm26 x).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x (NativeEntryCallerDispatch.Bl.word imm26) enc0 final = .ok () fin ∧
      fin.regs._Z = final.regs._Z := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have sysF : SysEq2 x.regs final.regs := EntryBranchPins.sysEq2_symm _ _ f.input.sys
  have controlsF := HeapV2StepCerts.BlStepV3.caller_controls_fetched x final hregs sysF controls
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, z⟩ :=
    RtB6.RichZ.bl_tailE real imm26 x low final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss controlsF
  exact ⟨fin, run, z⟩
end

section
variable {real : Type} [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {pbase : Nat} {table : Nat → Prop}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    {base : BitVec 64} {offset : Nat → BitVec 64} {bud : Nat} {k : Nat} {budget : Nat} {x : NativeState}

theorem z_stp
    (inv : RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
      scope image loadBase base offset bud k x)
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (spX : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp) (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    :
    ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table) x final budget →
    ∃ fin, nativeTail real x (NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7) enc0 final = .ok () fin ∧
      fin.regs._Z = final.regs._Z := by
  intro final enc0 f
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
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
    RtShim.SlotPrem.prem_shimStp final f.closed static post2F spF spAligned
  obtain ⟨sp, a, fin, _, _, hook, run, frame, _, _, _, _, _, _, _, _, _, np, _⟩ :=
    HeapV2StepCerts.MemTail.mem_tailD_Stp real spec config rows mapping x final enc0 0#7 9#5 30#5 (by decide)
      (by decide) (by decide +kernel) f.pins f.input f.guard budget f.quiet f.it f.ss f.current perAcc modeF debugF
      post2F featF.1 featF.2.1 featF.2.2.1 featF.2.2.2 dcacheF hsp hal pa mapped mmio outside (fun _ => True)
      (fun _ _ => trivial) (by rw [f.mem]; exact inv.raw)
      (fun acc sh => by rw [hostHAFT_eq sysF]; exact inv.noUpd true acc sh)
  exact ⟨fin, run, tail_z final sp a fin budget f.quiet hook _ _ frame rfl np⟩

theorem z_ldp
    (inv : RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table)
      scope image loadBase base offset bud k x)
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (present : RtShim.SlotPrem.ShimSlotPresent p mapping x)
    (spX : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp) (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    :
    ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping (HeapV2E17.consumerMapShim S p pbase mapping table) x final budget →
    ∃ fin, nativeTail real x (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7) enc0 final = .ok () fin ∧
      fin.regs._Z = final.regs._Z := by
  intro final enc0 f
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
  obtain ⟨sp, a, fin, _, _, hook, run, frame, _, _, _, _, _, _, _, _, _, np, _⟩ :=
    HeapV2StepCerts.MemTail.mem_tailD_Ldp real spec config rows mapping x final enc0 0#7 9#5 30#5 (by decide)
      (by decide) (by decide) (by decide +kernel) f.pins f.input f.guard budget f.quiet f.it f.ss f.current perAcc
      modeF debugF post2F featF.1 featF.2.1 featF.2.2.1 featF.2.2.2 dcacheF hsp hal pa mapped mmio data bytes
      (fun _ => False) (by rw [f.mem]; exact inv.raw)
      (fun acc sh => by rw [hostHAFT_eq sysF]; exact inv.noUpd false acc sh)
  exact ⟨fin, run, tail_z final sp a fin budget f.quiet hook _ _ frame rfl np⟩

end

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Release.shim_keep"
  (← IO.getStderr).flush

/-- Release.ShimKeep (H-P13k): frameRegs, X19 and _Z unchanged across the shim prologue (σ 0 → σ 7) and from the
body's final RET state to the caller return (σ 364 → σ 369). -/
theorem shim_keep (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (e : NativeState)
    (agrees : ConsumerMapAgrees spec mapping (shimMap spec mapping base pins))
    (room : 369 ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC j)
    (ob0 : FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word (stateAt real e 0))
    {w1 : BitVec 32} {writes1 : NativeEntry.Effects.Writes} {K1 : Int} {us1 : List (RegBind.Reg × RegBind.Upd)}
    (tail1 : RegValE.ClassTailVAt real w1 writes1 K1 (stateAt real e 1) ((stateAt real e 1).regs._PC + 4#64) us1)
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
    (bl7 : blTarget imm26 (stateAt real e 6) = base + offS 7) (low6 : (base + offS 7).toNat < 2 ^ 55)
    (ob6 : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) (stateAt real e 6))
    (pre : ShimPre real spec config rows mapping pins scope image loadBase base offS budget e)
    (callerPC : BitVec 64)
    (offPost : ∀ j, 365 ≤ j → j ≤ 368 → offS j = shimPC (j - 358))
    (bodyBudget : Nat) (dp : DeploymentPremises spec config rows mapping base pins (stateAt real e 7) bodyBudget)
    (hbB : 358 ≤ bodyBudget) (low365 : (base + offS 365).toNat < 2 ^ 55)
    (ob365 : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7)
      (stateAt real e 365))
    {w8 : BitVec 32} {writes8 : NativeEntry.Effects.Writes} {K8 : Int} {us8 : List (RegBind.Reg × RegBind.Upd)}
    (tail8 : RegValE.ClassTailVAt real w8 writes8 K8 (stateAt real e 366) ((stateAt real e 366).regs._PC + 4#64) us8)
    (ob8 : FetchObligations spec config rows mapping w8 (stateAt real e 366))
    (prof9 : NativeEntryAdapters.MsrDit.Profile (stateAt real e 367))
    (ob9 : FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) (stateAt real e 367))
    (low10 : (callerPC + 4#64).toNat < 2 ^ 55)
    (ob10 : FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) (stateAt real e 368))
    (ch : ShimChain real spec config rows mapping pins scope image loadBase base offS budget e callerPC)
    :
    ArmBridge.CruxGenGuarded.Release.ShimKeep real e := by
  have fr : ∀ r ∈ HeapV2StepCerts.Residue.frameRegs, r.val ≠ 9 ∧ r.val ≠ 30 := by decide
  have Ipre : ∀ j, j ≤ 6 → j < budget := fun j h => by omega
  have Ipost : ∀ j, (365 ≤ j ∧ j ≤ 368) → j < budget := fun j h => by omega
  have Z : ∀ j, j ≤ 6 → (stateAt real e (j + 1)).regs._Z = (stateAt real e j).regs._Z := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 0 (Ipre 0 (by omega))
        page (aligned 0) _ _ (pre.inv 0 (by omega)) ob0 (z_class (NativeShimTails.btiC_tailVAt real _) rfl))
    · exact ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 1 (Ipre 1 (by omega))
        page (aligned 1) _ _ (pre.inv 1 (by omega)) ob1 (z_classE tail1))
    · exact ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 2 (Ipre 2 (by omega))
        page (aligned 2) _ _ (pre.inv 2 (by omega)) ob2 (z_class (NativeShimTails.mrsDit9_tailVAt real _ prof2) rfl))
    · exact ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 3 (Ipre 3 (by omega))
        page (aligned 3) _ _ (pre.inv 3 (by omega)) ob3 (z_stp (pre.inv 3 (by omega)) static pre.sp3 spAligned))
    · exact ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 4 (Ipre 4 (by omega))
        page (aligned 4) _ _ (pre.inv 4 (by omega)) ob4 (z_class (NativeShimTails.ditOn_tailVAt real _ prof4) rfl))
    · exact ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 5 (Ipre 5 (by omega))
        page (aligned 5) _ _ (pre.inv 5 (by omega)) ob5 (z_class (NativeShimTails.isbSy_tailVAt real _ prof5) rfl))
    · exact ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 6 (Ipre 6 (by omega))
        page (aligned 6) _ _ (pre.inv 6 (by omega)) ob6 (z_bl imm26 controls6 (by rw [bl7]; exact low6)))
  have hE := e17_general real spec config rows mapping base pins (stateAt real e 7) bodyBudget dp (by omega)
  have inv357 := (hE.1 357 (by omega)).1
  have s364 : stateAt real e 364 = stateAt real (stateAt real e 7) 357 := stateAt_add real e 7 357
  have J364 := RtShim2.ShimBranch.shimInv_of_chainInv3 inv357.v3
  have fetch357 := MemNext.memFetch spec config rows mapping base bodyBudget 357 pins
    (rowsFootprint spec.imageRows).byte dp.static 0xc0 0xd65f03c0 (by decide +kernel) (by decide +kernel)
    (EntryBodyRet.W 30#5) (by decide) _ inv357.v3.v2
  have J365 := ch.inv 365 (Or.inr ⟨by omega, by omega⟩)
  have i366 := ch.inv 366 (Or.inr ⟨by omega, by omega⟩)
  have i367 := ch.inv 367 (Or.inr ⟨by omega, by omega⟩)
  have i368 := ch.inv 368 (Or.inr ⟨by omega, by omega⟩)
  have Z364 : (stateAt real e 365).regs._Z = (stateAt real e 364).regs._Z :=
    ev_succ (j := 364) (shim_z real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf bodyBudget 357
      (by omega) dp.page (by decide +kernel) _ _ (s364 ▸ J364) (s364 ▸ fetch357)
      (z_ret 30#5 (by decide) (by decide) (s364 ▸ J364).v2.v1.pins (s364 ▸ J364).v2.branch
        (by rw [ch.x30_364]; exact low365)))
  have Z365 : (stateAt real e 366).regs._Z = (stateAt real e 365).regs._Z :=
    ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 365
      (Ipost 365 ⟨by omega, by omega⟩) page (aligned 365) _ _ J365 ob365
      (z_ldp J365 static ch.present365 ch.sp365 spAligned))
  have Z366 : (stateAt real e 367).regs._Z = (stateAt real e 366).regs._Z :=
    ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 366
      (Ipost 366 ⟨by omega, by omega⟩) page (aligned 366) _ _ i366 ob8 (z_classE tail8))
  have Z367 : (stateAt real e 368).regs._Z = (stateAt real e 367).regs._Z :=
    ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 367
      (Ipost 367 ⟨by omega, by omega⟩) page (aligned 367) _ _ i367 ob9
      (z_class (NativeShimTails.msrDit9_tailVAt real _ prof9) rfl))
  have Z368 : (stateAt real e 369).regs._Z = (stateAt real e 368).regs._Z :=
    ev_succ (shim_z real spec config rows mapping _ scope image loadBase base offS budget 368
      (Ipost 368 ⟨by omega, by omega⟩) page (aligned 368) _ _ i368 ob10
      (z_ret 30#5 (by decide) (by decide) i368.v2.v1.pins i368.v2.branch
        (by show ((stateAt real e 368).regs.gpr[30]).toNat < _; rw [ch.x30_368]; exact low10)))
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ⟨fun r hr => ?_, ?_, ?_⟩⟩
  · simp only [RegBind.regVal]; exact pre.keepPre r (fr r hr).1 (fr r hr).2
  · show (stateAt real e 7).regs.gpr[19] = _
    exact pre.keepPre 19 (by decide) (by decide)
  · rw [Z 6 (by omega), Z 5 (by omega), Z 4 (by omega), Z 3 (by omega), Z 2 (by omega), Z 1 (by omega),
      Z 0 (by omega)]; rfl
  · simp only [RegBind.regVal]; exact ch.keepPost r (fr r hr).1 (fr r hr).2
  · show (stateAt real e 369).regs.gpr[19] = (stateAt real e 364).regs.gpr[19]
    exact ch.keepPost 19 (by decide) (by decide)
  · rw [Z368, Z367, Z366, Z365, Z364]

#print axioms shim_keep
end RtDit.Release
