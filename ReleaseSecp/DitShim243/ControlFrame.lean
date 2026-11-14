import RtPremC.Ctl
import TranslateSpan.DefaultScalarTrace
import TranslateSpan.DefaultFiniteMem
import TranslateSpan.DefaultRet
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmCertValue ArmCertPipe ArmCertMemPipe HeapV2StepCerts NativeAccess NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
open TranslateSpan
namespace DitShim243.ControlFrame

private theorem fields_of_frames (real : Type) [Sail.SailReal real]
    (word : BitVec 32) (K : Int) (source fetched sp action fin : NativeState)
    (budget : Nat) (input : NativeEntryInput.Input source fetched)
    (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    (frame : NativeEntryContract.Frame {} (actionState word sp K) action)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap action.regs fin.regs) :
    RtPremC.ctlv fin.regs = RtPremC.ctlv source.regs := by
  exact (RtPremC.ctl_np np).trans ((RtPremC.ctl_frame frame).trans
    ((RtPremC.ctl_action word sp K).trans ((RtPremC.ctl_e20 fetched sp budget quiet hook).trans
      (RtPremC.ctl_np input.controls.nonProj))))


theorem native_scalar (real : Type) [Sail.SailReal real]
    (word : BitVec 32) (K : Int) (source fetched fin : NativeState)
    (enc : __InstrEnc) (budget : Nat) (next : BitVec 64)
    (updates : List (HeapV2StepCerts.RegBind.Reg × Option VUpd))
    (flags : Option (VUpd × VUpd × VUpd × VUpd))
    (tail : ClassTailXAt real word {} K source next updates flags)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (actual : nativeTail real source word enc fetched = .ok () fin) :
    RtPremC.ctlv fin.regs = RtPremC.ctlv source.regs := by
  obtain ⟨sp,action,returned,hook,run,frame,finQuiet,finPins,sys,memory,gic,pc,np,events,z,values⟩ :=
    tail fetched enc budget pins input guard quiet it ss
  have same : returned = fin := congrArg (resSt source) (run.symm.trans actual)
  subst returned
  exact fields_of_frames real word K source fetched sp action fin budget input quiet hook frame np

theorem scalar_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (word : BitVec 32)
    (K : Int) (next : BitVec 64)
    (updates : List (HeapV2StepCerts.RegBind.Reg × Option VUpd))
    (flags : Option (VUpd × VUpd × VUpd × VUpd))
    (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping word source)
    (tail : ClassTailXAt real word {} K source next updates flags)
    (actual : modelStep real source = .ok () fin) :
    RtPremC.ctlv fin.regs = RtPremC.ctlv source.regs := by
  obtain ⟨fetched,enc,pins,input,guard,quiet,it,ss,run,choice⟩ :=
    DefaultScalarTrace.fetched_of_step real spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k room page aligned word source fin core ob actual
  exact native_scalar real word K source fetched fin enc (budget - (k+1)) next updates flags
    tail pins input guard quiet it ss run

theorem memory_tail (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow}
    {Ctx : NativeState → Prop} {D : Nat → Prop} {word : BitVec 32} {K : Int}
    {source : NativeState} {next : BitVec 64}
    {updates : List (RegBind.Reg × RegBind.Upd)}
    {Pay : NativeState → NativeState → Prop} {cost : Nat}
    (tail : DefaultEntryMem.MemTailAt real spec config rows Ctx D word {} K source next updates Pay cost) :
    DefaultEntryMem.MemTailAt real spec config rows Ctx D word {} K source next updates
      (fun fetched fin => Pay fetched fin ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv source.regs) cost := by
  intro fetched enc budget pins input guard quiet it ss current ctx
  obtain ⟨sp,action,fin,written,hook,run,frame,finQuiet,finPins,sys,memFrame,separated,inside,gic,pc,np,present,regs,pay,trace⟩ :=
    tail fetched enc budget pins input guard quiet it ss current ctx
  have fp := fields_of_frames real word K source fetched sp action fin budget input quiet hook frame np
  exact ⟨sp,action,fin,written,hook,run,frame,finQuiet,finPins,sys,memFrame,separated,inside,gic,pc,np,present,regs,
    ⟨pay,fp⟩,trace⟩

theorem memory_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget k : Nat} {profile : AccessProfile} {view : Physical.BytePA} {regions : List Region}
    {language : ValuePlan.Language} {σ0 : Sym} {inputs : List (BitVec 64)}
    {plan : List (ValuePlan.Step language)} {catalogue : ControlCatalogue}
    {entry : NativeState} {capacity : Nat} {drawsBefore : Nat → Nat} {cost : Nat}
    {x : NativeState} {D : Nat → Prop}
    (inv : DefaultMTE2.Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
      language view regions σ0 inputs plan entry capacity drawsBefore k x)
    (statusRoom : drawsBefore k < capacity) (statusBound : drawsBefore k + cost ≤ capacity)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sep : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    {word : BitVec 32} {K : Int} {next : BitVec 64}
    {updates : List (RegBind.Reg × RegBind.Upd)}
    {X Ctx : NativeState → Prop} {Pay : NativeState → NativeState → Prop}
    (adapt : ∀ f, DefaultEntryMem.FiniteFetchCtx spec config rows mapping m X catalogue cost f → Ctx f)
    (tail : DefaultEntryMem.MemTailAt real spec config rows Ctx D word {} K x next updates Pay cost)
    (xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay f g → Pay x g)
    (nextPlaced : next = base + offset (k+1))
    (ob : FetchObligations spec config rows mapping word x)
    (fin : NativeState) (actual : modelStep real x = .ok () fin) :
    RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have currentRows := DefaultMTE2.bounded_rows entry x capacity (drawsBefore k) cost
    inv.statusRows inv.trace statusBound
  have hq : HookQuiet ((budget - (k+1)) + 1) x := by
    have equal : budget - (k+1) + 1 = budget - k := by omega
    rw [equal]; exact inv.core.v1.quiet
  let StrongPay := fun before after => Pay before after ∧ RtPremC.ctlv after.regs = RtPremC.ctlv x.regs
  have strengthened : DefaultEntryMem.MemTailAt real spec config rows Ctx D word {} K x next updates StrongPay cost :=
    memory_tail real tail
  have transfer : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → StrongPay f g → StrongPay x g := by
    intro f g gpr sp memory flags pay
    exact ⟨xferPay f g gpr sp memory flags pay.1,pay.2⟩
  obtain ⟨other,run,pins,quiet,current,pc,debug,features,gic,closed,placed,bind,writing,pay,present,sys,br,tco,tls,z,delta⟩ :=
    DefaultEntryMem.entry_mem_next_choice real spec config rows mapping word {} K x inv.core.v1.pins next
      (offset (k+1)) updates m X D StrongPay catalogue cost Ctx
      (fun fetched ctx fetchedChoice => adapt fetched ⟨ctx,
        DefaultMTE2.rows_after_delta x fetched cost cost 0 currentRows fetchedChoice (by omega)⟩)
      strengthened inv.core.v1.gic inv.core.v1.features inv.core.v1.debug (budget-(k+1)) hq
      base (offset k) inv.core.v1.pc page aligned nextPlaced inv.core.v1.current inv.core.closed
      scope image loadBase inv.core.placed sep codeD inv.core.raw inv.core.noUpd xferX transfer
      inv.core.post inv.core.mode inv.core.controls
      (DefaultMTE2.bounded_status entry x capacity (drawsBefore k) inv.statusRows inv.trace statusRoom)
      inv.core.debug inv.core.feat inv.core.dcache ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have same : other = fin := congrArg (resSt x) (run.symm.trans actual)
  subst other
  exact pay.2

open ArmFull.Register
open ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryBodyRet

theorem native_ret (real : Type) [Sail.SailReal real] (source : NativeState) (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (W Rn) 31 12 == 879088#20) = false)
    (hlow : (source.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) (next : BitVec 64) :
    BranchFrameMTE2.BranchTailNZTZ real (W Rn) 94 source next (fun fin => fin.regs._PC = source.regs.gpr[(GPRSummary.key Rn.toNat).val] ∧
      RtPremC.ctlv fin.regs = RtPremC.ctlv source.regs) := by
  intro fetched enc0 budget pins bp input guard quiet it ss
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
  obtain ⟨fin, tail, _finalQuiet, _finalPins, _sys, _branch, output, _events, _gic, _, _pc, nonProj⟩ :=
    guarded_after_action_entry real source (W Rn) enc0 a budget aQuiet actionPins next enc eret
      actionIT actionSS
  have tpAction : ArmCertMemPipe.TLSFrame.tp a = ArmCertMemPipe.TLSFrame.tp fetched := by
    unfold ArmCertMemPipe.TLSFrame.tp
    rw [congrFun actFrame.b64 .TPIDR_EL0]
    change sp.regs.bank_BitVec_64 .TPIDR_EL0 = fetched.regs.bank_BitVec_64 .TPIDR_EL0
    exact frame_pres_E20 (fun r => r.bank_BitVec_64 .TPIDR_EL0)
      (fun r => by simp (disch := decide) only [eraseE20,RegMap.set_ne]) post.frame
  have tpKeep := (ArmCertMemPipe.TLSFrame.nonProj nonProj).trans tpAction
  have ps := (PMUFrame.of_E20 post.frame).pstate
  refine ⟨sp, fin, hook, prefixEq.trans tail, ?_, ?_, ?_, ?_, ?_, ?_,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 94).trans post.mem)),tpKeep,?_,?_⟩
  · rw [output.gpr, gprA]
    show sp.regs.gpr = _
    exact frame_pres_E20 (fun x => x.gpr) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [output.sp, spA]
    show sp.regs.SP_EL0 = _
    exact frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [output.n, congrArg ProcState.N psA]; show sp.regs.PSTATE.N = _; rw [ps]
  · rw [output.zf, congrArg ProcState.Z psA]; show sp.regs.PSTATE.Z = _; rw [ps]
  · rw [output.c, congrArg ProcState.C psA]; show sp.regs.PSTATE.C = _; rw [ps]
  · rw [output.v, congrArg ProcState.V psA]; show sp.regs.PSTATE.V = _; rw [ps]

  · rw [output.z]
    -- The actual branch action and its metadata/PMU prefix retain vector registers.
    have zAction := congrArg (fun r : Regs => r._Z) _npRun
    change a.regs._Z = fetched.regs._Z
    rw [show a.regs._Z = sp.regs._Z from zAction]
    exact frame_pres_E20 (fun r => r._Z)
      (fun r => by simp (disch := decide) only [eraseE20,RegMap.set_ne]) post.frame
  · refine ⟨?_,?_⟩
    · change fin.regs._PC = source.regs.gpr[(GPRSummary.key Rn.toNat).val]
      rw [_pc, _btRun, NativeEntryBodyBranch.Decide.ret_fBT_eq, if_pos rfl, _pcRun,
        NativeEntryBodyBranch.Decide.ret_fPC_eq, ← metadataInput.gpr]
    · exact (RtPremC.ctl_np nonProj).trans ((RtPremC.ctl_frameBr actFrame).trans
        (RtPremC.ctl_np metadataInput.controls.nonProj))


theorem ret_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (branch : BranchMTE2.Pins source) (Rn : BitVec 5) (valid : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (W Rn) 31 12 == 879088#20) = false)
    (low : (source.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (ob : FetchObligations spec config rows mapping (W Rn) source)
    (actual : modelStep real source = .ok () fin) :
    RtPremC.ctlv fin.regs = RtPremC.ctlv source.regs := by
  obtain ⟨fetched,enc,pins,input,guard,quiet,it,ss,run,choice⟩ :=
    DefaultScalarTrace.fetched_of_step real spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k room page aligned (W Rn) source fin core ob actual
  have br := ClassBranchPins.npe_branch source.regs fetched.regs input.controls.nonProj
  have fetchedBranch := BranchMTE2.pins_step source fetched branch
    (EntryBranchPins.sysEq2_symm _ _ input.sys) pins br
  obtain ⟨sp,other,hook,returned,gpr,stack,n,z,c,v,memory,tls,vectors,post⟩ :=
    native_ret real source Rn valid noEret low (source.regs._PC + 4#64)
      fetched enc (budget-(k+1)) pins fetchedBranch input guard quiet it ss
  have same : other = fin := congrArg (resSt source) (returned.symm.trans run)
  subst other
  exact post.2

#print axioms native_scalar
#print axioms scalar_step
#print axioms memory_tail
#print axioms memory_step
#print axioms native_ret
#print axioms ret_step
end DitShim243.ControlFrame
