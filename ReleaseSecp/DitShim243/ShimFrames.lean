import DitShim243.ShimABI
import DitShim243.BLFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts NativeMteTagCheck TranslateSpan ReleaseProfile
open NativeEntryCallerParts NativeEntryCallerTransport
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.ShimFrames
open ShimABI

theorem of_input {source fetched : NativeState} (input : NativeEntryInput.Input source fetched) : Fields source fetched :=
  ⟨ArmBridge.CruxNonProj.fFPCR input.controls.nonProj,ArmBridge.CruxNonProj.fFPSR input.controls.nonProj,
    input.z.symm,ArmCertMemPipe.TLSFrame.nonProj input.controls.nonProj⟩

theorem trans {a b c : NativeState} (ab : Fields a b) (bc : Fields b c) : Fields a c :=
  ⟨bc.fpcr.trans ab.fpcr,bc.fpsr.trans ab.fpsr,bc.z.trans ab.z,bc.tls.trans ab.tls⟩

theorem class_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (source fin : NativeState)
    (core : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase
      base offset budget k catalogue source)
    (word : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (next : BitVec 64)
    (updates : List (RegBind.Reg × RegBind.Upd))
    (tail : RegVal.ClassTailVAt real word writes K source next updates)
    (noFPCR : writes.fpcr = false) (noFPSR : writes.fpsr = false) (noVector : writes.vector = false)
    (ob : FetchObligations spec config rows mapping word source)
    (actual : modelStep real source = .ok () fin) : Fields source fin := by
  obtain ⟨fetched,enc,pins,input,guard,quiet,it,ss,run,choice,acc,nx,regs⟩ :=
    ShimABI.fetched_of_step real spec config rows mapping consumer scope image loadBase
      base offset budget catalogue k room page aligned word source fin core ob actual
  exact ShimABI.native_class real word K source fetched fin enc (budget-(k+1)) next updates writes
    tail noFPCR noFPSR noVector pins input guard quiet it ss run

theorem ret_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (source fin : NativeState)
    (core : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase
      base offset budget k catalogue source)
    (Rn : BitVec 5) (valid : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (low : (source.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (ob : FetchObligations spec config rows mapping (EntryBodyRet.W Rn) source)
    (actual : modelStep real source = .ok () fin) : Fields source fin := by
  obtain ⟨fetched,enc,pins,input,guard,quiet,it,ss,run,choice,acc,nx,regs⟩ :=
    ShimABI.fetched_of_step real spec config rows mapping consumer scope image loadBase
      base offset budget catalogue k room page aligned (EntryBodyRet.W Rn) source fin core ob actual
  have br := ClassBranchPins.npe_branch source.regs fetched.regs input.controls.nonProj
  have fetchedBranch := BranchMTE2.pins_step source fetched core.branch
    (EntryBranchPins.sysEq2_symm _ _ input.sys) pins br
  obtain ⟨sp,other,hook,returned,gpr,stack,n,z,c,v,memory,tls,vectors,post⟩ :=
    FPControlFrame.native_ret real source Rn valid noEret low (source.regs._PC + 4#64)
      fetched enc (budget-(k+1)) pins fetchedBranch input guard quiet it ss
  have same : other = fin := congrArg (resSt source) (returned.symm.trans run)
  subst other
  exact ⟨post.2.1,post.2.2,vectors.trans input.z.symm,
    tls.trans (ArmCertMemPipe.TLSFrame.nonProj input.controls.nonProj)⟩

theorem bl_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (source fin : NativeState)
    (core : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase
      base offset budget k catalogue source)
    (imm : BitVec 26) (controls : CallerControls source) (low : (blTarget imm source).toNat < 2 ^ 55)
    (ob : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm) source)
    (actual : modelStep real source = .ok () fin) : Fields source fin := by
  obtain ⟨fetched,enc,pins,input,guard,quiet,it,ss,run,choice,acc,nx,regs⟩ :=
    ShimABI.fetched_of_step real spec config rows mapping consumer scope image loadBase
      base offset budget catalogue k room page aligned (NativeEntryCallerDispatch.Bl.word imm) source fin core ob actual
  have sysF := EntryBranchPins.sysEq2_symm _ _ input.sys
  have controlsF := HeapV2StepCerts.BlStepV3.caller_controls_fetched source fetched regs sysF controls
  have target : blTarget imm fetched = blTarget imm source := by
    rw [NativeEntryCallerRegisters.bl_target,NativeEntryCallerRegisters.bl_target,input.pc]
  obtain ⟨other,returned,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,fields⟩ :=
    BLFrame.native_tail_ez real source fetched enc imm controlsF (by rw [target]; exact low)
      pins guard (budget-(k+1)) quiet it ss
  have same : other = fin := congrArg (resSt source) (returned.symm.trans run)
  subst other
  exact trans (of_input input) fields

#print axioms class_step
#print axioms ret_step
#print axioms bl_step
end DitShim243.ShimFrames
