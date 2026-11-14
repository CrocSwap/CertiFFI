import Bridge.CruxGenGuarded.EntryBodyRet
import HeapV2StepCerts.BranchFrame
import TranslateSpan.BranchFrameMTE2
import RtBr.RetDecode
import TranslateSpan.DefaultScalarTrace
import TranslateSpan.RetExitMTE2
import TranslateSpan.CurrentMemMTE2
import TranslateScalarTagCheck.Actions

namespace TranslateSpan.DefaultRet
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Boundary
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryBodyRet
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

theorem branch_of_input (source fetched : NativeState) (branch : BranchMTE2.Pins source)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) :
    BranchMTE2.Pins fetched := by
  exact BranchMTE2.pins_step source fetched branch
    (EntryBranchPins.sysEq2_symm _ _ input.sys) pins
    (ClassBranchPins.npe_branch _ _ input.controls.nonProj)

theorem tail_choice (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (W Rn) 31 12 == 879088#20) = false)
    (hlow : (source.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (branch : BranchMTE2.Pins source) :
    DefaultScalarTrace.TailChoiceAt real source (W Rn) := by
  intro fetched enc0 budget pins input guard quiet it ss fin actualRun
  have bp := branch_of_input source fetched branch pins input
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
  have bpT := BranchMTE2.pins_step fetched (actionState (W Rn) sp 94) bp
    (sysEq2_trans _ _ _ input.sys (EntryBranchPins.sysEq2_symm _ _ metadataInput.sys)) pinsT
    (EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_e20 _ _ post.frame)
      (EntryBranchPins.brSysEq_action (W Rn) sp 94))
  have hlowT : ((actionState (W Rn) sp 94).regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55 := by
    rw [← metadataInput.gpr]; exact hlow
  obtain ⟨a, action, actFrame, memRun, _eventsRun, btnRun, _pcRun, _btRun, physRun, _npRun, _gicRun, bttA,gprA,spA,psA⟩ :=
    BranchMTE2.run Rn hRn (actionState (W Rn) sp 94) bpT btnT hlowT
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
  have actionDelta := TranslateScalarTagCheck.Actions.action_20 Rn hRn
    (actionState (W Rn) sp 94) bpT.gcs () a action
  have prefixDelta : NativeMteTagCheck.ChoiceDelta fetched a 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans
        (NativeTagCheck.spec_choice_of_run (budget + 1) fetched sp quiet hook)
        (NativeTagCheck.metadata_choice (W Rn) sp 94)) actionDelta
  have tailDelta := NativeTagCheck.after_action_choice_of_run real source (W Rn) enc0 a fin
    budget aQuiet actionPins enc eret actionIT actionSS (prefixEq.symm.trans actualRun)
  simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans prefixDelta tailDelta

theorem terminal (real : Type) [Sail.SailReal real]
    {domain : ArmCert.Translate.Model.QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (separated : ImageTableSeparated scope loadBase mapping
      (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (x : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k x)
    (branch : BranchMTE2.Pins x) (room : k < budget)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (W Rn) 31 12 == 879088#20) = false)
    (originalLR : BitVec 64)
    (lrValue : x.regs.gpr[(GPRSummary.key Rn.toNat).val] = originalLR)
    (low : originalLR.toNat < 2 ^ 55)
    (fetch : FetchObligations spec config rows mapping (W Rn) x)
    (language : ArmCertPipe.ValuePlan.Language) (view : ArmCertValue.Physical.BytePA)
    (regions : List ArmCertValue.Region) (D : Nat → Prop) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ValuePlan.Holds language view regions
        (ArmCertPipe.ValuePlan.legacy language ⟨[],none,[]⟩) x fin ∧
      CurrentMTE2.BodyFrame D x fin ∧ fin.regs._PC = originalLR ∧
      NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have lowCurrent : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55 := by
    rw [lrValue]
    exact low
  obtain ⟨fin,run,gpr,sp,n,z,c,v,memory,tls,vectors,pc⟩ :=
    RetExitMTE2.step real spec config rows mapping consumer scope image loadBase separated
      base offset budget k x core.v1 core.closed core.placed branch core.raw core.noUpd
      room page aligned Rn hRn noEret lowCurrent fetch
  have delta := DefaultScalarTrace.step_choice real spec config rows mapping consumer
    scope image loadBase base offset budget profile catalogue k room page aligned (W Rn) x fin
    core fetch (tail_choice real x Rn hRn noEret lowCurrent branch) run
  have value := TranslateStepV.BranchX.vholds_nil gpr sp n z c v
  have effect : ArmCertPipe.ValuePlan.Holds language view regions
      (ArmCertPipe.ValuePlan.legacy language ⟨[],none,[]⟩) x fin := by
    exact (ArmCertPipe.ValuePlan.holds_legacy language view regions ⟨[],none,[]⟩ x fin).mpr
      ⟨value,ArmCertValue.Physical.memV_nil_of_mem view regions x fin memory⟩
  refine ⟨fin,run,effect,⟨?_,vectors,tls⟩,pc.trans lrValue,delta⟩
  intro address outside
  rw [memory]

#print axioms terminal

#print axioms branch_of_input
#print axioms tail_choice
end TranslateSpan.DefaultRet
