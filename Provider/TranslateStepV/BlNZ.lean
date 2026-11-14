-- the heap-v2 BL step facts (k = 15, 150, 252) for stepV_k. CallerBl.native_tail_ez
-- (RtB6.BlTailZ) re-run with the NZCV carry added (NativeEntryCallerParts.bl_action_PSTATE + the PMU E20 frame), as
-- BlTailNZ; entry_bl_next_X = RtB3.RichH.entry_class_next_v3_blL reduced to the value frame; bl_vholds concludes
-- VHolds [(.x 30, none)] none (X30 clobbered, every other GPR, SP and NZCV kept) and memory kept.
import Bridge.CruxGenGuarded.EntryBl
import Bridge.CruxGenGuarded.ClosedChain
import RtB3.RichH
import TranslateStepV.BranchX
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
namespace TranslateStepV.BlNZ
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.CallerBl NativeEntryCallerParts NativeEntryCallerTransport
open HeapV2StepCerts.BranchStepV3
open ArmBridge.CruxGenGuarded.ClosedChain
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false

/-- The BL tail over the fetched state, reduced to the value frame: X30 = PC + 4, other GPRs, SP, NZCV, memory kept. -/
def BlTailNZ (real : Type) [Sail.SailReal real] (imm26 : BitVec 26) (source : NativeState) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched →
    MetadataGuard fetched → HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true → CallerControls fetched →
    ∃ fin, nativeTail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched = .ok () fin ∧
      fin.regs.gpr = fetched.regs.gpr.set 30 (source.regs._PC + 4#64) ∧ fin.regs.SP_EL0 = fetched.regs.SP_EL0 ∧
      fin.regs.PSTATE.N = fetched.regs.PSTATE.N ∧ fin.regs.PSTATE.Z = fetched.regs.PSTATE.Z ∧
      fin.regs.PSTATE.C = fetched.regs.PSTATE.C ∧ fin.regs.PSTATE.V = fetched.regs.PSTATE.V ∧
      fin.mem = fetched.mem

set_option maxHeartbeats 100000 in
set_option maxRecDepth 512 in
/-- native_tail_ez proof, concluding the value frame plus NZCV. -/
theorem tail_nz (real : Type) [Sail.SailReal real] (imm26 : BitVec 26) (source : NativeState)
    (low : (blTarget imm26 source).toNat < 2 ^ 55) : BlTailNZ real imm26 source := by
  intro fetched enc0 budget spins input guard quiet it ss controls
  have pcEq : fetched.regs._PC = source.regs._PC := input.pc
  have low : (blTarget imm26 fetched).toNat < 2 ^ 55 := by
    have t : blTarget imm26 fetched = blTarget imm26 source := by
      rw [NativeEntryCallerRegisters.bl_target, NativeEntryCallerRegisters.bl_target, pcEq]
    rw [t]; exact low
  have pins : EntryPins fetched := NativeEntryTail.EntryPins.of_scalar fetched spins
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have ps := NativeEntryTail.EntryPins.after_E20 fetched sp pins post.frame
  have pc := caller_controls_after_E20 fetched sp controls post.frame
  let a := actionState (NativeEntryCallerDispatch.Bl.word imm26) sp 68
  have ca : CallerControls a := caller_controls_at_metadata sp (NativeEntryCallerDispatch.Bl.word imm26) 68 pc
  have pa : EntryPins a := entryPins_at_metadata sp (NativeEntryCallerDispatch.Bl.word imm26) 68 ps
  have qa : HookQuiet (budget + 1) a := actionState_quiet (NativeEntryCallerDispatch.Bl.word imm26) sp 68 (budget + 1) post.quiet
  have specOut := e20_output fetched sp post.frame post.mem
  have metadataOut := caller_metadata_output sp (NativeEntryCallerDispatch.Bl.word imm26) 68
  have target : blTarget imm26 a = blTarget imm26 fetched := by
    rw [NativeEntryCallerRegisters.bl_target, NativeEntryCallerRegisters.bl_target]
    change sp.regs._PC + _ = fetched.regs._PC + _
    rw [(PMUFrame.of_E20 post.frame).pc]
  have lowA : (blTarget imm26 a).toNat < 2^55 := by rw [target]; exact low
  have encA : a.regs.__ThisInstrEnc = .__A64 := by rfl
  have eretA : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false :=
    word_not_eret imm26
  have itA : a.regs.ShouldAdvanceIT = false := (PMUFrame.of_E20 post.frame).it.trans it
  have ssA : a.regs.ShouldAdvanceSS = true := (PMUFrame.of_E20 post.frame).ss.trans ss
  have dispatch : DispatchAt real (NativeEntryCallerDispatch.Bl.word imm26) (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) 68 := by
    intro pc t see
    exact NativeEntryCallerDispatch.Bl.dispatch_at real pc imm26 t (by simpa using see)
  have metadataBoundary := metadata_boundary_at real source (NativeEntryCallerDispatch.Bl.word imm26) (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) enc0 sp
    (guard.after_E20 post.frame) 68 (by decide) dispatch
  obtain ⟨fin, run, _qfin, _pfin, _btype, _next, _sys, _branch, out, _events, _gic, _dit, _finalPC,
    memory, gpr, _lr, _frame⟩ :=
    bl_action_tail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 imm26 a budget ca lowA qa pa encA eretA itA ssA
  have pcA : a.regs._PC = fetched.regs._PC := (PMUFrame.of_E20 post.frame).pc
  have gprA : a.regs.gpr = fetched.regs.gpr := metadataOut.gpr.trans specOut.gpr
  have linkA : NativeEntryCallerRegisters.linkValue a = fetched.regs._PC + 4#64 := by
    rw [NativeEntryCallerRegisters.link_value, pcA]
  have psF := (PMUFrame.of_E20 post.frame).pstate
  refine ⟨fin, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    memory.trans ((actionState_mem (NativeEntryCallerDispatch.Bl.word imm26) sp 68).trans post.mem)⟩
  · exact (spec_pmu_boundary real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched sp hook).trans (metadataBoundary.trans run)
  · rw [gpr, gprA, linkA, pcEq]
  · rw [out.sp, bl_action_SP_EL0]
    show sp.regs.SP_EL0 = _
    exact frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [out.n, bl_action_PSTATE]; show sp.regs.PSTATE.N = _; rw [psF]
  · rw [out.zf, bl_action_PSTATE]; show sp.regs.PSTATE.Z = _; rw [psF]
  · rw [out.c, bl_action_PSTATE]; show sp.regs.PSTATE.C = _; rw [psF]
  · rw [out.v, bl_action_PSTATE]; show sp.regs.PSTATE.V = _; rw [psF]

#print axioms tail_nz

set_option maxHeartbeats 200000 in
/-- RtB3.RichH.entry_class_next_v3_blL with the value-frame tail. -/
theorem entry_bl_next_X (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (imm26 : BitVec 26)
    (s : NativeState) (stepPins : StepPins s)
    (tail : BlTailNZ real imm26 s) (controls : CallerControls s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (placedImg : MemReloc.ImageOn scope image s loadBase mapping)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState s) acc →
      domain (queryOf acc) ∧ ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data
          (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (code : ∀ acc leafLevel view faultOut (address : AddressDescriptor) translated (word' : BitVec 32),
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view
        (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)) (faultOut, address) translated →
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (word'.extractLsb' (8 * i) 8)) →
      word' = NativeEntryCallerDispatch.Bl.word imm26) :
    ∃ fin, modelStep real s = .ok () fin ∧ fin.regs.gpr = s.regs.gpr.set 30 (s.regs._PC + 4#64) ∧
      fin.regs.SP_EL0 = s.regs.SP_EL0 ∧
      fin.regs.PSTATE.N = s.regs.PSTATE.N ∧ fin.regs.PSTATE.Z = s.regs.PSTATE.Z ∧
      fin.regs.PSTATE.C = s.regs.PSTATE.C ∧ fin.regs.PSTATE.V = s.regs.PSTATE.V ∧ fin.mem = s.mem := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, _fev, _curFinal, _, _info, _walk, _leaf, _middle, _len, _traffic, _tev, noUpdCond⟩ :=
    native_fetch_current_preserving_events spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, rawOf acc]; rfl
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final _ pins hGIC run emuFinal
  have fpins := EntryClassNext.fetched_steppins acc (translateCurrent out) s final stepPins hregs
  have finput := fetched_input acc (translateCurrent out) s final pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final (budget + 1) pins quiet hregs
  have sysF : SysEq2 s.regs final.regs := EntryBranchPins.sysEq2_symm _ _ finput.sys
  have controlsF := RtB2.RichG.caller_controls_fetched s final hregs sysF controls
  obtain ⟨fin, tail, gprF, spF, nF, zF, cF, vF, mem⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss controlsF
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem :=
    (noUpdCond rawS (by
      rw [rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)).2.2
  have finMem : fin.mem = s.mem := mem.trans (fmem.trans memNoUpd)
  rw [hregs] at gprF spF nF zF cF vF
  exact ⟨fin, hstep.trans tail,
    by rw [gprF, ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl],
    spF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    nF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.N) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    zF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    cF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.C) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    vF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.V) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    finMem⟩

#print axioms entry_bl_next_X

/-- VHolds of the BL plan entry [(.x 30, none)]: X30 clobbered, every other GPR, SP and NZCV kept. -/
theorem vholds_bl {x y : NativeState} (v : BitVec 64) (g : y.regs.gpr = x.regs.gpr.set 30 v)
    (sp : y.regs.SP_EL0 = x.regs.SP_EL0)
    (n : y.regs.PSTATE.N = x.regs.PSTATE.N) (z : y.regs.PSTATE.Z = x.regs.PSTATE.Z)
    (c : y.regs.PSTATE.C = x.regs.PSTATE.C) (v' : y.regs.PSTATE.V = x.regs.PSTATE.V) :
    ArmCertValue.VHolds [(.x 30, none)] none x y := by
  refine ⟨fun r => ?_, fun i => ?_⟩
  · rcases r with ⟨i, hi⟩ | _
    · by_cases h : i = 30
      · subst h; simp
      · have hd : decide (HeapV2StepCerts.RegBind.Reg.x 30 = .x ⟨i, hi⟩) = false :=
          decide_eq_false (fun e => by cases e; exact h rfl)
        simp only [List.find?, hd, Option.map_none]
        simp only [HeapV2StepCerts.RegBind.regVal, g]
        simp [Vector.getElem_set, show (30 : Nat) ≠ i from fun e => h e.symm]
    · simp [HeapV2StepCerts.RegBind.regVal, sp]
  · match i with
    | 0 => simp only [ArmCertValue.flagWord, n]
    | 1 => simp only [ArmCertValue.flagWord, z]
    | 2 => simp only [ArmCertValue.flagWord, c]
    | 3 => simp only [ArmCertValue.flagWord, v']

/-- A BL step (plan entry ⟨[(.x 30, none)], none, []⟩) from ChainInv3 at k and the caller controls. -/
theorem bl_vholds (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm26 : BitVec 26)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (controls : CallerControls x) (tail : BlTailNZ real imm26 x)
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [(.x 30, none)] none x fin ∧ fin.mem = x.mem := by
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, g, sp, n, z, c, v, mem⟩ :=
    entry_bl_next_X real spec config rows mapping imm26 x inv.v2.v1.pins tail controls inv.v2.v1.gic
      inv.v2.v1.features inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, vholds_bl _ g sp n z c v, mem⟩

#print axioms bl_vholds

end TranslateStepV.BlNZ
