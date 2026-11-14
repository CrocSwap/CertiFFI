import LoopNative.BranchFrame
import Bridge.CruxGenGuarded.EntryBodyRet
import RtBranch.BranchTailsX
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryBodyRet ArmBridge.CruxGenBr Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace LoopNative.RetABI
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false

theorem noEret (Rn : BitVec 5) :
    (Sail.BitVec.extractLsb (W Rn) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (W Rn) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 11) h
    simp only [W, NativeEntryBodyDispatch.Ret.selected, NativeEntryBodyDispatch.Ret.word,
      Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne

/-- Same actual RET decoder/prefix/tail, retaining source->fin register mask. -/
theorem tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (hlow : (source.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) :
    BranchFrame.Tail real (W Rn) 94 source source.regs.gpr[(GPRSummary.key Rn.toNat).val] := by
  intro fetched enc0 budget pins bp input guard quiet it ss
  have noEret := noEret Rn

  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (W Rn) 94
  have metadataQuiet := actionState_quiet (W Rn) sp 94 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (W Rn) 94
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have btypeT : (actionState (W Rn) sp 94).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btnT : (actionState (W Rn) sp 94).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have pinsT : StepPins (actionState (W Rn) sp 94) := scalar_pins _ metaPins btypeT btnT
  have bpT := EntryBranchPins.branch_pins_action source fetched sp (W Rn) 94 input metadataInput
    post.frame pinsT bp
  have hlowT : ((actionState (W Rn) sp 94).regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55 := by
    rw [← metadataInput.gpr]; exact hlow
  obtain ⟨a, action, actFrame, memRun, eventsRun, btnRun, pcRun, btRun, physRun, npRun, gicRun, bttA⟩ :=
    NativeEntryBodyBranch.Ret.run Rn hRn (actionState (W Rn) sp 94) bpT btnT hlowT
  have dispatch : DispatchAt real (W Rn) (A Rn) 94 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Ret.dispatch_at real pc Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (W Rn) (A Rn) enc0 sp currentGuard 94
    (by decide) dispatch
  have prefixEq : nativeTail real source (W Rn) enc0 fetched =
      nativeAfterAction real source (W Rn) enc0 a := by
    calc
      nativeTail real source (W Rn) enc0 fetched =
          afterSpecPmu real source (W Rn) enc0 sp :=
        spec_pmu_boundary real source (W Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (W Rn) (A Rn) enc0 (actionState (W Rn) sp 94) := boundary
      _ = nativeAfterAction real source (W Rn) enc0 a :=
        action_boundary real source (W Rn) (A Rn) enc0 (actionState (W Rn) sp 94) a action
  have actionPinsStep : StepPins a :=
    actbr_pins (actionState (W Rn) sp 94) a pinsT actFrame bttA
  have actionPins := NativeEntryTail.EntryPins.of_scalar a actionPinsStep
  have next : a.regs.BTypeNext = 0#2 := btnRun.trans btnT
  have enc : a.regs.__ThisInstrEnc = .__A64 := actFrame.enc.trans (by rfl)
  have eret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [actFrame.b32]
    simpa (disch := decide) only [actionState, RegMap.set_ne, RegMap.set_same] using noEret
  have actionIT : a.regs.ShouldAdvanceIT = false :=
    actFrame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : a.regs.ShouldAdvanceSS = true :=
    actFrame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  have fields : GuardFieldsEq (actionState (W Rn) sp 94) a :=
    ⟨actFrame.feat, by simpa using congrArg ProcState.EL actFrame.pse,
     by simpa using congrArg ProcState.nRW actFrame.pse, actFrame.bbool _ (by decide),
     congrFun actFrame.bint _, congrFun actFrame.b32 _, physRun, fun k _ => congrFun actFrame.b64 k⟩
  have aQuiet : HookQuiet (budget + 1) a := quiet_of_fields (budget + 1) _ a metadataQuiet fields
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, branch, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (W Rn) enc0 a budget aQuiet actionPins next enc eret
      actionIT actionSS
  have actionPC : (actionState (W Rn) sp 94).regs._PC = source.regs._PC := metadataInput.pc
  have bf := Crypto.CruxRet.ret_regs real (actionState (W Rn) sp 94) a Rn hRn action bpT hlowT btnT
  have gprF : fin.regs.gpr = fetched.regs.gpr := by
    rw [output.gpr, bf.1]
    show sp.regs.gpr = _
    exact frame_pres_E20 (fun x => x.gpr) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have spF : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [output.sp, bf.2]
    show sp.regs.SP_EL0 = _
    exact frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have gicF : fin.regs.bank_Option_InterruptID .__GIC_Pending = fetched.regs.bank_Option_InterruptID .__GIC_Pending := by
    rw [gic, gicRun]
    show sp.regs.bank_Option_InterruptID .__GIC_Pending = _
    exact post.gic
  have pcFin : fin.regs._PC = source.regs.gpr[(GPRSummary.key Rn.toNat).val] := by
    rw [pc, btRun, NativeEntryBodyBranch.Decide.ret_fBT_eq, if_pos rfl, pcRun,
      NativeEntryBodyBranch.Decide.ret_fPC_eq, ← metadataInput.gpr]
  exact ⟨sp, a, fin, hook, prefixEq.trans tail, actFrame, finalQuiet, finalPins, sys, branch,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 94).trans post.mem)), gicF, pcFin, nonProj, gprF, spF,
    ArmCertCT.CT2.NonProjRegsEq.trans
      (ArmCertCT.CT2.NonProjRegsEq.trans metadataInput.controls.nonProj npRun) nonProj⟩

#print axioms noEret
#print axioms tail
theorem next_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (nextPlaced : x.regs.gpr[(GPRSummary.key Rn.toNat).val] = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (W Rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      fin.mem = x.mem ∧ fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
      NativeEntry.Effects.Frame {} x.regs fin.regs ∧ fin.regs._PC = x.regs.gpr[(GPRSummary.key Rn.toNat).val] := by
  have framed := tail real x Rn hRn hlow
  have kept := BranchFrame.frameG real spec config rows mapping m scope image loadBase separated base offset budget
    (fun _ _ => True) k room page aligned (W Rn) 94 (fun t => t.regs.gpr[(GPRSummary.key Rn.toNat).val])
    x inv framed nextPlaced obligations
  obtain ⟨fin, run, nextInv, memory, gpr, sp, _⟩ := RtG.nextG_branch real spec config rows mapping m scope image loadBase
    separated base offset budget (fun _ _ => True) k room page aligned (W Rn) 94
    (fun t => t.regs.gpr[(GPRSummary.key Rn.toNat).val]) x inv (BranchFrame.toTail framed)
    nextPlaced obligations (fun _ _ _ _ _ => True.intro)
  exact ⟨fin, run, nextInv, memory, gpr, sp, kept fin run, nextInv.v2.v1.pc.trans nextPlaced.symm⟩
#print axioms next_abi

end LoopNative.RetABI
