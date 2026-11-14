import N1D226.SubShiftBorrow.Frame
import N1D226.SubShiftBorrow.Dispatch
import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import Bridge.CruxGenGuarded.EntryControls
import NativeEntryInput.Input
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace N1D226.SubShiftBorrow.Tail
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false

theorem noEret (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : (Sail.BitVec.extractLsb (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have bit := congrArg (fun v => v.getLsbD 11) h
  simp only [N1D226.SubShiftBorrow.Encoding.selected,N1D226.SubShiftBorrow.Encoding.word,Sail.BitVec.extractLsb,
    BitVec.extractLsb,BitVec.getLsbD_extractLsb',BitVec.getLsbD_append] at bit
  simp at bit

theorem dispatch (real : Type) [Sail.SailReal real] (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) :
    DispatchAt real (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 0#1 1#1 1#1) 16 := by
  intro pc t see
  rw [N1D226.SubShiftBorrow.Encoding.selected,N1D226.SubShiftBorrow.Dispatch.dispatch real pc Rm imm6 Rn Rd]
  have h : (t.regs.bank_Int .SEE <b 16) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 16)) : SailM Bool) t =
      .ok (t.regs.bank_Int .SEE <b 16) t := rfl
  rw [ArmBridge.CruxCore.bind_app,read]
  dsimp only []
  rw [if_pos h]

/-- Actual post-fetch native tail; all later guards and runs are constructed here. -/
theorem native_tail (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ sp act fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16) ∧
      nativeTail real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched = .ok () fin ∧
      N1D226.SubShiftBorrow.projection act = N1D226.SubShiftBorrow.expected (actionState (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16) Rd Rn imm6 Rm ∧
      NativeEntryContract.Frame {} (actionState (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16) act ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 act.regs fin.regs ∧ BrSysEq act.regs fin.regs ∧ CongOut fin act ∧
      fin.mem = fetched.mem ∧ fin.events = fetched.events ∧
      fin.regs._PC = source.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap act.regs fin.regs ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap source.regs fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = act.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.PSTATE.DIT = act.regs.PSTATE.DIT := by
  obtain ⟨sp,hook,post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) 16
  have metadataQuiet := actionState_quiet (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16 (budget + 1) post.quiet
  have metadataPins := metadata_pins (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16 (e20_pins fetched sp pins post.frame)
  obtain ⟨act,action,projection,frame,actionQuiet,actionMem,actionEvents,btn⟩ :=
    N1D226.SubShiftBorrow.Frame.run (actionState (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16) Rd Rn imm6 Rm rd rn rm metadataPins (budget + 1) metadataQuiet
  have boundary := metadata_boundary_at real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 0#1 1#1 1#1) enc0 sp currentGuard 16 (by decide) (dispatch real Rd Rn imm6 Rm)
  have nativePrefix : nativeTail real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched = nativeAfterAction real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 act := by
    calc
      nativeTail real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched = afterSpecPmu real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 sp :=
        spec_pmu_boundary real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched sp hook
      _ = nativeAtAction real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 0#1 1#1 1#1) enc0 (actionState (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16) := boundary
      _ = nativeAfterAction real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 act :=
        action_boundary real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 0#1 1#1 1#1) enc0 (actionState (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16) act action
  have ep := entryPins_at_metadata sp (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) 16
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have ap := NativeEntryTail.EntryPins.after_action frame ep
  have next : act.regs.BTypeNext = 0#2 := by
    rw [btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have enc : act.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (act.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    exact noEret Rd Rn imm6 Rm
  have actionIT : act.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : act.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  obtain ⟨fin,tail,q,p,sys,br,out,ev,gic,dit,pc,np⟩ :=
    guarded_after_action_entry real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 act budget actionQuiet ap next enc eret actionIT actionSS
  have nobranch : act.regs.__BranchTaken = false := frame.bt
  have actPC : act.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have actionNonProj := (NativeEntry.Effects.scalar_iff _ _).mp frame.nonProj
  have nonProj : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap source.regs fin.regs :=
    (metadataInput.controls.nonProj.trans actionNonProj).trans np
  refine ⟨sp,act,fin,hook,metadataInput,nativePrefix.trans tail,projection,frame,q,p,sys,br,out,?_,?_,?_,np,nonProj,gic,dit⟩
  · exact out.mem.trans (actionMem.trans ((actionState_mem (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16).trans post.mem))
  · exact ev.trans (actionEvents.trans ((actionState_events (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16).trans post.events))
  · simpa only [nobranch,Bool.false_eq_true,ite_false,actPC] using pc

#print axioms noEret
#print axioms dispatch
#print axioms native_tail
end N1D226.SubShiftBorrow.Tail
