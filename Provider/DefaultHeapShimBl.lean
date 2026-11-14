-- Actual BL, preserving the current controls, GCS, SIMD and event records.
import RtBl.BlStepV3
import RtB4.EvShapeBridge
import CurrentInv
import HeapControl
import DefaultCallChoice

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ReleaseProfile.DefaultHeapShimBl
open ArmBridge.CruxGenGuarded.CallerBl
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded NativeEntryCallerParts NativeEntryCallerTransport
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.CallerBl.native_tail_ez"
  (← IO.getStderr).flush

theorem native_tail_ez (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm26 : BitVec 26)
    (controls : CallerControls fetched)
    (low : (blTarget imm26 fetched).toNat < 2^55)
    (spins : StepPins fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin,
      nativeTail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched = .ok () fin ∧
      HookQuiet budget fin ∧ StepPins fin ∧
      SysEq2 fetched.regs fin.regs ∧ BrSysEq fetched.regs fin.regs ∧
      fin.mem = fetched.mem ∧
      fin.regs._PC = blTarget imm26 fetched ∧
      fin.regs.gpr = fetched.regs.gpr.set 30 (fetched.regs._PC + 4#64) ∧
      fin.regs.SP_EL0 = fetched.regs.SP_EL0 ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = fetched.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.bank_Int .__block_bbm_implemented = fetched.regs.bank_Int .__block_bbm_implemented ∧
      fin.regs.bank_BitVec_64 .PIR_EL2 = fetched.regs.bank_BitVec_64 .PIR_EL2 ∧
      fin.regs.bank_BitVec_64 .PIRE0_EL2 = fetched.regs.bank_BitVec_64 .PIRE0_EL2 ∧
      fin.regs.bank_BitVec_64 .POR_EL0 = fetched.regs.bank_BitVec_64 .POR_EL0 ∧
      fin.regs.bank_BitVec_64 .SCR_EL3 = fetched.regs.bank_BitVec_64 .SCR_EL3 ∧
      fin.events = fetched.events ∧ fin.regs._Z = fetched.regs._Z ∧
      fin.regs.PSTATE.TCO = fetched.regs.PSTATE.TCO ∧ NativeMteTagCheck.ChoiceDelta fetched fin 0 ∧ fin.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT := by
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
  obtain ⟨fin, run, qfin, pfin, btype, next, sys, branch, out, events, gic, dit, finalPC,
    memory, gpr, lr, frame⟩ :=
    bl_action_tail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 imm26 a budget ca lowA qa pa encA eretA itA ssA
  have btnA : a.regs.BTypeNext = fetched.regs.BTypeNext := by
    change sp.regs.BTypeNext = fetched.regs.BTypeNext
    exact (PMUFrame.of_E20 post.frame).btn
  have pcA : a.regs._PC = fetched.regs._PC := (PMUFrame.of_E20 post.frame).pc
  have gprA : a.regs.gpr = fetched.regs.gpr := metadataOut.gpr.trans specOut.gpr
  have linkA : NativeEntryCallerRegisters.linkValue a = fetched.regs._PC + 4#64 := by
    rw [NativeEntryCallerRegisters.link_value, pcA]
  have actualRun : nativeTail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched = .ok () fin :=
    (spec_pmu_boundary real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched sp hook).trans
      (metadataBoundary.trans run)
  have prefixRun : nativeTail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched =
      nativeAfterAction real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 (blActionState imm26 a) :=
    (spec_pmu_boundary real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched sp hook).trans
      (metadataBoundary.trans (action_boundary real source (NativeEntryCallerDispatch.Bl.word imm26)
        (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) enc0 a
        (blActionState imm26 a) (bl_run imm26 a ca lowA)))
  have finalChoice := NativeTagCheck.native_tail_choice_of_delta real source fetched sp (blActionState imm26 a) fin
    (NativeEntryCallerDispatch.Bl.word imm26) enc0 68 budget 0 quiet hook
    (DefaultCallChoice.bl_choice imm26 a ca lowA) prefixRun
    (bl_quiet imm26 a (budget + 1) qa) (bl_pins imm26 a pa)
    ((bl___ThisInstrEnc imm26 a).trans encA)
    (by rw [bl_bank_BitVec_32]; exact eretA)
    ((bl_ShouldAdvanceIT imm26 a).trans itA) ((bl_ShouldAdvanceSS imm26 a).trans ssA) actualRun
  have b64 : ∀ k : Bank_BitVec_64, ArmBridge.CruxNonProj.bkHeap.b64 k = false →
      (∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k) →
      fin.regs.bank_BitVec_64 k = fetched.regs.bank_BitVec_64 k := by
    intro k hk he
    rw [ClosedChain.np_b64 frame k hk, congrFun (bl_bank_BitVec_64 imm26 a) k]
    show sp.regs.bank_BitVec_64 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_64 k) he post.frame
  refine ⟨fin, ?_, qfin, scalar_pins fin pfin (btype.trans (btnA.trans spins.btn)) (next.trans (btnA.trans spins.btn)),
    sysEq2_trans _ _ _ (e20_sys _ _ post.frame)
      (sysEq2_trans _ _ _ (caller_metadata_sys sp (NativeEntryCallerDispatch.Bl.word imm26) 68 ps) sys),
    brSysEq_trans _ _ _ (e20_branch _ _ post.frame)
      (brSysEq_trans _ _ _ (caller_metadata_branch sp (NativeEntryCallerDispatch.Bl.word imm26) 68) branch),
    memory.trans ((actionState_mem (NativeEntryCallerDispatch.Bl.word imm26) sp 68).trans post.mem),
    finalPC.trans target, ?_, ?_, ?_, ?_,
    b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]),
    b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]),
    b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]),
    b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]),
    events.trans ((actionState_events (NativeEntryCallerDispatch.Bl.word imm26) sp 68).trans post.events), ?_, ?_, finalChoice, ?_⟩
  · exact (spec_pmu_boundary real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched sp hook).trans (metadataBoundary.trans run)
  · rw [gpr, gprA, linkA]
  · rw [out.sp, bl_action_SP_EL0]
    show sp.regs.SP_EL0 = _
    exact frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [gic]
    show sp.regs.bank_Option_InterruptID .__GIC_Pending = _
    exact post.gic
  · rw [ClosedChain.np_int frame _ (by decide), congrFun (bl_bank_Int imm26 a) _]
    simp (disch := decide) only [a, actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => x.bank_Int .__block_bbm_implemented) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [out.z, bl_action__Z]
    show sp.regs._Z = _
    exact frame_pres_E20 (fun x => x._Z) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame

  · have tco := congrArg (fun r : Regs => r.PSTATE.TCO) frame
    have act : (blActionState imm26 a).regs.PSTATE.TCO = a.regs.PSTATE.TCO :=
      congrArg ProcState.TCO (bl_action_PSTATE imm26 a)
    exact tco.trans (act.trans (congrArg ProcState.TCO (PMUFrame.of_E20 post.frame).pstate))
  · have tco := congrArg (fun r : Regs => r.PSTATE.DIT) frame
    have act : (blActionState imm26 a).regs.PSTATE.DIT = a.regs.PSTATE.DIT :=
      congrArg ProcState.DIT (bl_action_PSTATE imm26 a)
    exact tco.trans (act.trans (congrArg ProcState.DIT (PMUFrame.of_E20 post.frame).pstate))

#print axioms native_tail_ez


open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts.BlStepV3
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false


#check "CURRENT_DECL entry_bl"
set_option maxHeartbeats 200000 in
theorem entry_bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (imm26 : BitVec 26)
    (s : NativeState) (stepPins : StepPins s) (nextOffset : BitVec 64)
    (low : (blTarget imm26 s).toNat < 2 ^ 55) (controls : CallerControls s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (nextPlaced : blTarget imm26 s = base + nextOffset)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (placedImg : MemReloc.ImageOn scope image s loadBase mapping)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (bp : TranslateSpan.BranchMTE2.Pins s)
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (code : ∀ acc leafLevel view faultOut (address : AddressDescriptor) translated (word' : BitVec 32),
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view
        (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)) (faultOut, address) translated →
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (word'.extractLsb' (8 * i) 8)) →
      word' = NativeEntryCallerDispatch.Bl.word imm26) :
    ∃ fin,
      modelStep real s = .ok () fin ∧
      StepPins fin ∧ HookQuiet budget fin ∧
      CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      fin.regs._PC = base + nextOffset ∧
      E11Debug.E11CheckDebug fin.regs ∧ EntryFeatures fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = none ∧
      ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      MemReloc.ImageOn scope image fin loadBase mapping ∧
      TranslateSpan.BranchMTE2.Pins fin ∧
      (fin.regs.gpr = s.regs.gpr.set 30 (s.regs._PC + 4#64)) ∧ fin.regs.SP_EL0 = s.regs.SP_EL0 ∧ fin.mem = s.mem ∧
      SysEq2 s.regs fin.regs ∧ fin.regs.PSTATE.TCO = s.regs.PSTATE.TCO ∧
      fin.regs._Z = s.regs._Z ∧
      fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 ∧
      StepEvents.EvShape spec mapping [] s fin ∧ RtPremC.CtlRel spec s fin ∧
      NativeMteTagCheck.ChoiceDelta s fin 0 ∧ fin.regs.PSTATE.DIT = s.regs.PSTATE.DIT := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, _fev, curFinal, _, _info, _walk, _leaf, _middle, _len, _traffic, _tev, noUpdCond⟩ :=
    native_fetch_current_preserving_events spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  have closedFinal := closed_membership_after_fetch closed clean fregs
  have placedFinal := HeapV2StepCerts.placed_fetch placedImg separated clean fmem
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
  have controlsF := caller_controls_fetched s final hregs sysF controls
  have bpFinal := TranslateSpan.BranchMTE2.pins_step s final bp sysF fpins
    (EntryFetchedBranch.fetched_brSysEq acc (translateCurrent out) s final hregs)
  have target : blTarget imm26 final = blTarget imm26 s := by
    rw [NativeEntryCallerRegisters.bl_target, NativeEntryCallerRegisters.bl_target, finput.pc]
  obtain ⟨fin, tail, finQuiet, finStep, sys, brsys, mem, pc, gprF, spF, gicF, bbm, pir, pire0, por,
      gcs, ev, z, tco, tailChoice, dit⟩ :=
    native_tail_ez real s final enc0 imm26 controlsF (by rw [target]; exact low) fpins guard budget fquiet it ss
  have curFin : CurrentS1At spec config rows fin := by
    refine current_s1_program_write curFinal (fun _ => False) (EntryBtiNext.no_writes final fin mem)
      (EntryBtiNext.no_writes_separated _) sys.feat sys.el sys.nrw sys.tcr sys.tcr2 sys.hcr sys.scr sys.sctlr
      sys.mair sys.pa (fun _ => pir) (fun _ => pire0) (fun _ => por) sys.tlb
  have mdscrFinal : final.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .MDSCR_EL1) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have hdeFinal : _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR)) _ _ s
      (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne, RegMap.set_same]
    exact ArmBridge.CruxCore.hde_pipeadv _ _
  have featFin : fin.regs.FeatureImpl = s.regs.FeatureImpl := sys.feat.trans sysF.feat
  have gicFin : fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
    rw [gicF, hregs]
    rw [ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_Option_InterruptID .__GIC_Pending) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact hGIC
  have closedFin := ClosedChain.closed_of_fields closedFinal sys.feat sys.tcr sys.sctlr sys.ttbr0 sys.httbr sys.ttbr1 bbm
  have placedFin := HeapV2StepCerts.placed_class mem placedFinal
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem :=
    (noUpdCond rawS (by
      rw [rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)).2.2
  have finMem : fin.mem = s.mem := mem.trans (fmem.trans memNoUpd)
  have gprFinal : final.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have sysS : SysEq2 s.regs fin.regs := sysEq2_trans _ _ _ sysF sys
  have bpFin := TranslateSpan.BranchMTE2.pins_step final fin bpFinal sys finStep brsys
  have events := RtB4.EvShapeBridge.evShape_of_fetchRun spec config rows mapping _ s fin stepPins features debug current
    (pc_low_of_placement _ base offset placed page word) ⟨queryOf, rawOf, vaOf, mmio, present, perAcc, code⟩
    rawS noUpdS nodup ⟨final, _, run, ev⟩
  rw [hregs] at tco z gcs dit
  have tcoF := EntryBtiNext.fetched_field (fun r => r.PSTATE.TCO) acc (translateCurrent out) s
    (fun _ _ => rfl) (fun _ => rfl) rfl
  have ditF := EntryBtiNext.fetched_field (fun r => r.PSTATE.DIT) acc (translateCurrent out) s
    (fun _ _ => rfl) (fun _ => rfl) rfl
  have zF := EntryBtiNext.fetched_field (fun r => r._Z) acc (translateCurrent out) s
    (fun _ _ => rfl) (fun _ => rfl) rfl
  have gcsF := EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .SCR_EL3) acc (translateCurrent out) s
    (fun _ _ => rfl) (fun _ => rfl) (by simp (disch := decide) only [beforeFetchState, RegMap.set_ne])

  have fetchedChoice := HeapControl.fetch_choice real spec config rows mapping
    (NativeEntryCallerDispatch.Bl.word imm26) s final stepPins features debug base offset placed page word current
    ⟨queryOf, rawOf, vaOf, mmio, present, perAcc, code⟩ ⟨_, run⟩
  have finalChoice : NativeMteTagCheck.ChoiceDelta s fin 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans fetchedChoice tailChoice
  have ctl : RtPremC.ctlv fin.regs = RtPremC.ctlv final.regs := by
    simp only [RtPremC.ctlv, sys.feat, sys.el, sys.nrw, sys.tlb, sys.tcr, sys.tcr2,
      sys.hcr, sys.scr, sys.sctlr, sys.mair, sys.httbr, pir, pire0, por,
      sys.ttbr0, sys.ttbr1, sys.pa, bbm]
  have control : RtPremC.CtlRel spec s fin := RtPremC.CtlRel.of_mem
    (ctl.trans (by rw [hregs]; exact RtPremC.ctl_fetched acc _ s)) finMem
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin, closed_before_fetch fin closedFin, placedFin, bpFin, (by rw [gprF, gprFinal, finput.pc]), spF.trans spFinal, finMem, sysS,
    tco.trans tcoF, z.trans zF, gcs.trans gcsF, events, control, finalChoice, dit.trans ditF⟩
  · rw [pc, target, nextPlaced]
  · rw [sys.mdscr, mdscrFinal]; exact debug.mde
  · rw [sys.hde, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms entry_bl


end ReleaseProfile.DefaultHeapShimBl
