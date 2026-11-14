import DitShim243.ShimABI
import DitShim243.SlotMem
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts NativeMteTagCheck ReleaseProfile
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.ShimMemoryFrames

theorem strengthen (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow}
    {Ctx : NativeState → Prop} {D : Nat → Prop} {word : BitVec 32} {K : Int}
    {writes : NativeEntry.Effects.Writes} {source : NativeState} {next : BitVec 64}
    {updates : List (RegBind.Reg × RegBind.Upd)} {Pay : NativeState → NativeState → Prop}
    {data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)} {cost : Nat}
    (tail : DefaultHeapShimEntry.MemTailDefaultAt real spec config rows Ctx D word writes K source next updates Pay data cost)
    (noFPCR : writes.fpcr = false) (noFPSR : writes.fpsr = false) (noVector : writes.vector = false) :
    DefaultHeapShimEntry.MemTailDefaultAt real spec config rows Ctx D word writes K source next updates
      (fun fetched fin => Pay fetched fin ∧ ShimABI.Fields source fin) data cost := by
  intro fetched enc budget pins input guard quiet it ss current ctx
  obtain ⟨sp,action,fin,written,hook,run,frame,q,fp,sys,mem,sep,inside,gic,pc,np,present,regs,pay,ev,z,nz,draws,delta,bound⟩ :=
    tail fetched enc budget pins input guard quiet it ss current ctx
  have fields := ShimABI.fields_of_frames real word K source fetched sp action fin budget input quiet hook frame noFPCR noFPSR noVector np
  exact ⟨sp,action,fin,written,hook,run,frame,q,fp,sys,mem,sep,inside,gic,pc,np,present,regs,⟨pay,fields⟩,ev,z,nz,draws,delta,bound⟩

theorem memory_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat) (catalogue : ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (status : TagStatusRows x (x.choiceOcc.getD 1354 0) 1)
    (slot : RtShim.SlotPrem.ShimSlotPresent p mapping x) (spAt : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (Pay : NativeState → NativeState → Prop)
    (payT : ∀ f y, f.regs.gpr = x.regs.gpr → f.mem = x.mem → Pay f y → Pay x y)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (us : List (RegBind.Reg × RegBind.Upd))
    (noWriteDit : writes.dit = false)
    (noFPCR : writes.fpcr = false) (noFPSR : writes.fpsr = false) (noVector : writes.vector = false)
    (tail : DefaultHeapShimEntry.MemTailDefaultAt real spec config rows
      (DefaultHeapShimEntry.ShimCtx spec config rows mapping m p catalogue 1)
      D w writes K x (x.regs._PC + 4#64) us Pay data 1)
    (target : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x)
    (fin : NativeState) (actual : modelStep real x = .ok () fin) : ShimABI.Fields x fin := by
  let StrongPay := fun before after => Pay before after ∧ ShimABI.Fields x after
  have transfer : ∀ f y, f.regs.gpr = x.regs.gpr → f.mem = x.mem → StrongPay f y → StrongPay x y := by
    intro f y gpr memory pay
    exact ⟨payT f y gpr memory pay.1,pay.2⟩
  obtain ⟨other,run,_,_,_,_,pay,_,_,_,_,_,_,_⟩ := SlotMem.shim_mem_step real spec config rows mapping m scope image loadBase
    separated base offset budget p k catalogue room page aligned x inv status slot spAt D codeD StrongPay transfer data nodup
    w writes K us noWriteDit (strengthen real tail noFPCR noFPSR noVector) target ob
  have same : other = fin := congrArg (resSt x) (run.symm.trans actual)
  subst other
  exact pay.2

#print axioms strengthen
#print axioms memory_step
end DitShim243.ShimMemoryFrames
