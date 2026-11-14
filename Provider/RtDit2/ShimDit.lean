-- (H-P4 + D180a (2), /): the shim's DIT-relevant step facts over ShimInv
-- (fetch obligations and per-class Profiles are hypotheses; synthetic instance after the relink).
-- entry_gen: the actual fetch (keeps DIT/mem/GPRs/SP) + any tail fact Q. Per kind:
--   shim_class  (s0 BTI, s1 SUB SP, s5 ISB, s8 ADD SP): DIT, mem kept, Holds us
--   shim_mrs9   (s2 MRS X9, DIT): X9 = (0 ++ DIT) ++ 0#24, DIT and mem kept
--   shim_stp    (s3 STP X9, X30, [SP]): the slot holds stpData (X9 low, X30 high), DIT kept, only the slot written
--   shim_ditOn  (s4 MSR DIT, #1): DIT = 1, mem and GPRs kept
--   shim_bl / shim_ret (s6 BL, body RET, s10 RET): DIT and mem kept
--   shim_ldp    (s7 LDP X9, X30, [SP]): X9 = ldpLo of the slot's 16 bytes, DIT kept
--   shim_msr9   (s9 MSR DIT, X9): DIT = X9[24], mem kept
import NativeShimTails.Tails
import RtS3.MemTailP2
import RtSaved.MemTailP
import RtSaved.SlotCore
import RtShim2.ShimMem
import RtDit2.BranchM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts HeapV2StepCerts.MemNext
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace RtDit.Shim
open RtDit NativeEntryCallerParts

theorem ok_inj {real : Type} [Sail.SailReal real] {m : SailM Unit} {s a b : NativeState}
    (h1 : m s = .ok () a) (h2 : m s = .ok () b) : a = b := by
  rw [h1] at h2; injection h2

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.entry_gen"
  (← IO.getStderr).flush

theorem entry_gen (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (s : NativeState) (stepPins : StepPins s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (ob : FetchObligations spec config rows mapping w s) (Q : NativeState → NativeState → Prop)
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ Q final fin) :
    ∃ final fin, modelStep real s = .ok () fin ∧ final.regs.PSTATE.DIT = s.regs.PSTATE.DIT ∧
      final.mem = s.mem ∧ final.regs.gpr = s.regs.gpr ∧ final.regs.SP_EL0 = s.regs.SP_EL0 ∧ Q final fin := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, _fev, curFinal, _, _info, _walk, _leaf, _middle, _len, _traffic, _tev, noUpdCond⟩ :=
    native_fetch_current_preserving_events spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc
  have hw := ob.code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  have closedFinal := closed_membership_after_fetch closed clean fregs
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, ob.rawOf acc]; rfl
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final _ pins hGIC run emuFinal
  have fpins := EntryClassNext.fetched_steppins acc (translateCurrent out) s final stepPins hregs
  have finput := fetched_input acc (translateCurrent out) s final pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final (budget + 1) pins quiet hregs
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem :=
    (noUpdCond rawS (by
      rw [ob.rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)).2.2
  have finalMem : final.mem = s.mem := fmem.trans memNoUpd
  have ditFinal : final.regs.PSTATE.DIT = s.regs.PSTATE.DIT := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.DIT) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl
  have gprFinal : final.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  obtain ⟨fin, tailRun, q⟩ := tail final enc0
    ⟨fpins, finput, guard, fquiet, it, ss, curFinal, closedFinal, finalMem, ⟨acc, _, hregs⟩⟩
  exact ⟨final, fin, hstep.trans tailRun, ditFinal, finalMem, gprFinal, spFinal, q⟩

/-- entry_gen at a ShimInv state. -/
theorem shim_gen (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (x : NativeState)
    (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
    (ob : FetchObligations spec config rows mapping w x) (Q : NativeState → NativeState → Prop)
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping m x final (budget - (k + 1)) →
      ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ Q final fin) :
    ∃ final fin, modelStep real x = .ok () fin ∧ final.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      final.mem = x.mem ∧ final.regs.gpr = x.regs.gpr ∧ final.regs.SP_EL0 = x.regs.SP_EL0 ∧ Q final fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  exact entry_gen real spec config rows mapping w x inv.v2.v1.pins inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug
    (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned inv.v2.v1.current m inv.v2.closed inv.raw
    inv.noUpd ob Q tail

section
variable (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (x : NativeState)
    (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
include room page aligned inv

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_class"
  (← IO.getStderr).flush

/-- s0 BTI c, s1 SUB SP, s5 ISB, s8 ADD SP (any fixed-class tail not writing DIT). -/
theorem shim_class {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)}
    (tail : RegVal.ClassTailVAt real w writes K x next us) (hw : writes.dit = false)
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ fin.mem = x.mem ∧
      RegBind.Holds us x fin := by
  obtain ⟨final, fin, run, dF, mF, gF, sF, dit, mem, holds⟩ :=
    shim_gen real spec config rows mapping m scope image loadBase base offset budget k room page aligned w x inv ob
      (fun final fin => fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT ∧ fin.mem = final.mem ∧ RegBind.Holds us final fin)
      (fun final enc0 f => by
        obtain ⟨sp, a, fin, hook, run, frame, _, _, _, mem, _, _, np, holds⟩ :=
          tail final enc0 _ f.pins f.input f.guard f.quiet f.it f.ss
        exact ⟨fin, run, tail_dit final sp a fin _ f.quiet hook w K frame hw np, mem, holds⟩)
  exact ⟨fin, run, dit.trans dF, mem.trans mF, RegBind.Holds.of_prefix gF sF holds⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_mrs9"
  (← IO.getStderr).flush

/-- s2 MRS X9, DIT. -/
theorem shim_mrs9 (profile : NativeEntryAdapters.MrsDit.Profile x)
    (ob : FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.gpr[9] = (0#39 +++ x.regs.PSTATE.DIT) +++ 0#24 ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ fin.mem = x.mem := by
  obtain ⟨final, fin, run, dF, mF, _, _, x9, dit, mem⟩ :=
    shim_gen real spec config rows mapping m scope image loadBase base offset budget k room page aligned _ x inv ob
      (fun final fin => fin.regs.gpr[9] = (0#39 +++ final.regs.PSTATE.DIT) +++ 0#24 ∧
        fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT ∧ fin.mem = final.mem)
      (fun final enc0 f => by
        obtain ⟨fin, run, x9, dit⟩ :=
          NativeShimTails.mrsDit9_dit real x final enc0 profile f.pins f.input f.guard _ f.quiet f.it f.ss
        obtain ⟨_, _, fin2, _, run2, _, _, _, _, mem, _⟩ :=
          NativeShimTails.mrsDit9_tailVAt real x profile final enc0 _ f.pins f.input f.guard f.quiet f.it f.ss
        have e := ok_inj (real := real) run run2
        subst e
        exact ⟨fin, run, x9, dit, mem⟩)
  exact ⟨fin, run, by rw [x9, dF], dit.trans dF, mem.trans mF⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_ditOn"
  (← IO.getStderr).flush

/-- s4 MSR DIT, #1. -/
theorem shim_ditOn (profile : NativeEntryAdapters.DitOn.Profile x)
    (ob : FetchObligations spec config rows mapping NativeEntryDispatch.DitOn.word x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = 1#1 ∧ fin.mem = x.mem ∧
      RegBind.Holds [] x fin := by
  obtain ⟨final, fin, run, _, mF, gF, sF, dit, mem, holds⟩ :=
    shim_gen real spec config rows mapping m scope image loadBase base offset budget k room page aligned _ x inv ob
      (fun final fin => fin.regs.PSTATE.DIT = 1#1 ∧ fin.mem = final.mem ∧ RegBind.Holds [] final fin)
      (fun final enc0 f => by
        obtain ⟨fin, run, dit⟩ :=
          NativeShimTails.ditOn_dit real x final enc0 profile f.pins f.input f.guard _ f.quiet f.it f.ss
        obtain ⟨_, _, fin2, _, run2, _, _, _, _, mem, _, _, _, holds⟩ :=
          NativeShimTails.ditOn_tailVAt real x profile final enc0 _ f.pins f.input f.guard f.quiet f.it f.ss
        have e := ok_inj (real := real) run run2
        subst e
        exact ⟨fin, run, dit, mem, holds⟩)
  exact ⟨fin, run, dit, mem.trans mF, RegBind.Holds.of_prefix gF sF holds⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_msr9"
  (← IO.getStderr).flush

/-- s9 MSR DIT, X9. -/
theorem shim_msr9 (profile : NativeEntryAdapters.MsrDit.Profile x)
    (ob : FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.gpr[9].extractLsb 24 24 ∧
      fin.mem = x.mem := by
  obtain ⟨final, fin, run, _, mF, gF, _, dit, mem⟩ :=
    shim_gen real spec config rows mapping m scope image loadBase base offset budget k room page aligned _ x inv ob
      (fun final fin => fin.regs.PSTATE.DIT = final.regs.gpr[9].extractLsb 24 24 ∧ fin.mem = final.mem)
      (fun final enc0 f => by
        obtain ⟨fin, run, dit⟩ :=
          NativeShimTails.msrDit9_dit real x final enc0 profile f.pins f.input f.guard _ f.quiet f.it f.ss
        obtain ⟨_, _, fin2, _, run2, _, _, _, _, mem, _⟩ :=
          NativeShimTails.msrDit9_tailVAt real x profile final enc0 _ f.pins f.input f.guard f.quiet f.it f.ss
        have e := ok_inj (real := real) run run2
        subst e
        exact ⟨fin, run, dit, mem⟩)
  exact ⟨fin, run, by rw [dit, gF], mem.trans mF⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_bl"
  (← IO.getStderr).flush

/-- s6 BL into the body. -/
theorem shim_bl (imm26 : BitVec 26) (controls : CallerControls x) (low : (blTarget imm26 x).toNat < 2 ^ 55)
    (ob : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      MemFrame (fun _ => False) x fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  exact entry_ditM real spec config rows mapping _ x inv.v2.v1.pins inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug
    (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned inv.v2.v1.current m inv.v2.closed inv.raw
    inv.noUpd ob _ (dit_blM real imm26 controls low _)

/-- RET Rn (s10 exit; the body's final RET is RtDit.dit_body_ret). -/
theorem shim_ret (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (ob : FetchObligations spec config rows mapping (EntryBodyRet.W Rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      MemFrame (fun _ => False) x fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  exact entry_ditM real spec config rows mapping _ x inv.v2.v1.pins inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug
    (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned inv.v2.v1.current m inv.v2.closed inv.raw
    inv.noUpd ob _ (dit_retM real Rn hRn noEret inv.v2.v1.pins inv.v2.branch _ hlow)
end

/-- The shim slot (16 bytes at the PA of SP = p.sp) holds the bytes of d. -/
def SlotHas (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (d : BitVec 128) (s : NativeState) : Prop :=
  ∀ n, mapping (BitVec.ofNat 64 p.sp) = some n → ∀ i < 16, s.mem[n + i]? = some (d.extractLsb' (8 * i) 8)

section
variable (real : Type) [Sail.SailReal real]
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
include room page aligned inv static spX spAligned

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_stp"
  (← IO.getStderr).flush

/-- s3 STP X9, X30, [SP]: the slot then holds stpData (X9 at +0, X30 at +8); only the slot is written. -/
theorem shim_stp (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      SlotHas p mapping (ArmCertMem.StpEval.stpData x 9#5 30#5) fin ∧
      MemFrame (RtShim2.ShimMem.slotBytes p mapping) x fin := by
  obtain ⟨final, fin, run, dF, mF, gF, _, dit, slot, fr⟩ :=
    shim_gen real spec config rows mapping _ scope image loadBase base offset budget k room page aligned _ x inv ob
      (fun final fin => fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT ∧
        SlotHas p mapping (ArmCertMem.StpEval.stpData final 9#5 30#5) fin ∧
        MemFrame (RtShim2.ShimMem.slotBytes p mapping) final fin)
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
        obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
          RtShim.SlotPrem.prem_shimStp final f.closed static post2F spF spAligned
        have inD : ∀ i < 16, RtShim2.ShimMem.slotBytes p mapping (pa.toNat + i) := fun i hi =>
          ⟨pa.toNat, by rw [← hva]; exact mapped, by omega, by omega⟩
        obtain ⟨sp, a, fin, written, _, hook, run, frame, _, _, _, wo, _, _, _, _, _, np, _, _, inW, pay⟩ :=
          RtSaved.MemTailP.mem_tailP_Stp real spec config rows mapping x final enc0 0#7 9#5 30#5 (by decide) (by decide)
            (by decide +kernel) f.pins f.input f.guard _ f.quiet f.it f.ss f.current perAcc modeF debugF post2F
            featF.1 featF.2.1 featF.2.2.1 featF.2.2.2 dcacheF hsp hal pa mapped mmio outside
            (RtShim2.ShimMem.slotBytes p mapping) inD (by rw [f.mem]; exact inv.raw)
            (fun acc sh => by rw [hostHAFT_eq sysF]; exact inv.noUpd true acc sh)
        refine ⟨fin, run, tail_dit final sp a fin _ f.quiet hook _ _ frame rfl np, ?_,
          fun y hy => wo y (fun h => hy (inW y h))⟩
        intro n hn i hi
        rw [← hva, mapped] at hn
        obtain rfl : pa.toNat = n := Option.some.inj hn
        exact pay i hi)
  have sd : ArmCertMem.StpEval.stpData final 9#5 30#5 = ArmCertMem.StpEval.stpData x 9#5 30#5 := by
    unfold ArmCertMem.StpEval.stpData; rw [gF]
  refine ⟨fin, run, dit.trans dF, sd ▸ slot, fun a ha => (fr a ha).trans (by rw [mF])⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_ldp"
  (← IO.getStderr).flush

/-- s7 LDP X9, X30, [SP]: X9 := the low half of the slot's 16 bytes. -/
theorem shim_ldp (present : RtShim.SlotPrem.ShimSlotPresent p mapping x)
    (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      ∀ d : BitVec 128, SlotHas p mapping d x → fin.regs.gpr[9] = ArmCertMem.LdpEval.ldpLo d := by
  obtain ⟨final, fin, run, dF, mF, _, _, dit, lo⟩ :=
    shim_gen real spec config rows mapping _ scope image loadBase base offset budget k room page aligned _ x inv ob
      (fun final fin => fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT ∧
        ∀ d : BitVec 128, SlotHas p mapping d final → fin.regs.gpr[9] = ArmCertMem.LdpEval.ldpLo d)
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
        obtain ⟨sp, a, fin, written, _, hook, run, frame, _, _, _, _, _, _, _, _, _, np, _, _, _, _, lo⟩ :=
          RtSaved3.MemTailP2.mem_tailP2_Ldp real spec config rows mapping x final enc0 0#7 9#5 30#5 (by decide)
            (by decide) (by decide) (by decide +kernel) f.pins f.input f.guard _ f.quiet f.it f.ss f.current perAcc
            modeF debugF post2F featF.1 featF.2.1 featF.2.2.1 featF.2.2.2 dcacheF hsp hal pa mapped mmio data bytes
            (fun _ => False) (by rw [f.mem]; exact inv.raw)
            (fun acc sh => by rw [hostHAFT_eq sysF]; exact inv.noUpd false acc sh)
        refine ⟨fin, run, tail_dit final sp a fin _ f.quiet hook _ _ frame rfl np, ?_⟩
        intro d hd
        have hn : mapping (BitVec.ofNat 64 p.sp) = some pa.toNat := by rw [← hva]; exact mapped
        have same : data = d := RtSaved.bytes_ext (fun i hi =>
          Option.some.inj ((bytes i hi).symm.trans (hd pa.toNat hn i hi)))
        rw [← same]; exact lo)
  refine ⟨fin, run, dit.trans dF, fun d hd => lo d (fun n hn i hi => by rw [mF]; exact hd n hn i hi)⟩
end

#print axioms entry_gen
#print axioms shim_class
#print axioms shim_mrs9
#print axioms shim_ditOn
#print axioms shim_msr9
#print axioms shim_bl
#print axioms shim_ret
#print axioms shim_stp
#print axioms shim_ldp
end RtDit.Shim
