import TranslateSpan.EntryMemMTE2

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue ArmCertMemPipe HeapV2StepCerts NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.CurrentMTE2

structure BodyFrame (D : Nat → Prop) (x fin : NativeState) : Prop where
  writes : WritesOnly D (fun pa => x.mem[pa]?) (fun pa => fin.mem[pa]?)
  z : fin.regs._Z = x.regs._Z
  tls : fin.regs.bank_BitVec_64 .TPIDR_EL0 = x.regs.bank_BitVec_64 .TPIDR_EL0

theorem mem_next (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget k : Nat} {profile : AccessProfile} {view : Physical.BytePA} {regions : List Region}
    {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List ArmCertValue.F.Step}
    {x : NativeState} {D : Nat → Prop}
    (inv : Inv spec config rows mapping m scope image loadBase base offset budget profile view regions σ0 inputs plan k x)
    (room : k < budget) (roomPlan : k < plan.length)
    (compiles : (ArmCertValue.F.compileRun regions σ0 inputs.length plan).isSome = true)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sep : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (tableD : Separated (rowsFootprint spec.imageRows).byte D)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)}
    {X Ctx : NativeState → Prop} {Pay : NativeState → NativeState → Prop}
    (adapt : ∀ f, EntryMemMTE2.TcoFetchCtx spec config rows mapping m X f → Ctx f)
    (tail : MemTailGAt real spec config rows Ctx D w writes K x next us Pay)
    (xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay f g → Pay x g)
    (noVector : writes.vector = false)
    (nextPlaced : next = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x)
    (effectOf : ∀ fin, RegBind.Holds us x fin → Pay x fin → ArmCertValue.F.Holds view regions plan[k] x fin) :
    ∃ fin, modelStep real x = .ok () fin ∧
      Inv spec config rows mapping m scope image loadBase base offset budget profile
        view regions σ0 inputs plan (k + 1) fin ∧
      ArmCertValue.F.Holds view regions plan[k] x fin ∧ BodyFrame D x fin := by
  have hq : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.core.v1.quiet
  obtain ⟨fin,run,pins,quiet,current,pc,debug,features,gic,closed,_,bind,⟨written,frame,_,sub⟩,pay,_,sys,br,tco,tls,z⟩ :=
    EntryMemMTE2.entry_mem_next real spec config rows mapping w writes K x inv.core.v1.pins next
      (offset (k + 1)) us m X D Pay Ctx adapt tail inv.core.v1.gic inv.core.v1.features
      inv.core.v1.debug (budget - (k + 1)) hq base (offset k) inv.core.v1.pc page aligned nextPlaced
      inv.core.v1.current inv.core.closed scope image loadBase inv.core.placed sep codeD inv.core.raw
      inv.core.noUpd xferX xferPay inv.core.post inv.core.mode inv.core.profileAt.host inv.core.mte2 inv.core.tco
      inv.core.debug inv.core.feat inv.core.dcache ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have wo := frame.mono sub
  have effect := effectOf fin bind pay
  exact ⟨fin,run,of_pair_effect inv roomPlan compiles ⟨pins,features,debug,current,quiet,gic,pc⟩
    closed sys br tco wo tableD codeD effect,effect,⟨wo,z noVector,tls⟩⟩

#print axioms mem_next
end TranslateSpan.CurrentMTE2
