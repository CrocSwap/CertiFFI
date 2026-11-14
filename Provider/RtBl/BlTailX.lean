-- Core's CallerBl.native_tail (EntryBl.lean) with the
-- extra fetched → fin carries the ChainInv v3 BL step needs: StepPins, GIC pending, SP_EL0, and the
-- non-SysEq2 fields closed membership / CurrentS1At read (bbm, PIR_EL2, PIRE0_EL2, POR_EL0).
import Bridge.CruxGenGuarded.EntryBl
import Bridge.CruxGenGuarded.ClosedChain
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded.CallerBl
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded NativeEntryCallerParts NativeEntryCallerTransport
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.CallerBl.native_tail_x"
  (← IO.getStderr).flush

theorem native_tail_x (real : Type) [Sail.SailReal real]
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
      fin.regs.bank_BitVec_64 .POR_EL0 = fetched.regs.bank_BitVec_64 .POR_EL0 := by
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
    b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne])⟩
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

#print axioms native_tail_x
end ArmBridge.CruxGenGuarded.CallerBl
