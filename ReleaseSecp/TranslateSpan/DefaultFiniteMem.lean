import TranslateSpan.DefaultEntryMem
import TranslateSpan.DefaultFiniteRows
import TranslateSpan.DefaultPairJoin
import TranslateSpan.CurrentMemMTE2

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue ArmCertPipe ArmCertMemPipe HeapV2StepCerts NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.DefaultEntryMem

structure FiniteFetchCtx {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (X : NativeState → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (cost : Nat) (fetched : NativeState)
    extends DefaultFetchCtx spec config rows mapping m X catalogue fetched : Prop where
  statusRows : NativeMteTagCheck.TagStatusRows fetched (fetched.choiceOcc.getD 1354 0) cost

end TranslateSpan.DefaultEntryMem

namespace TranslateSpan.DefaultMTE2

theorem mem_next_finite (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget k : Nat} {profile : AccessProfile} {view : Physical.BytePA} {regions : List Region}
    {language : ValuePlan.Language}
    {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List (ValuePlan.Step language)}
    {catalogue : NativeMteTagCheck.ControlCatalogue}
    {entry : NativeState} {capacity : Nat} {drawsBefore : Nat → Nat} {cost : Nat}
    {x : NativeState} {D : Nat → Prop}
    (inv : Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
      language view regions σ0 inputs plan entry capacity drawsBefore k x)
    (statusRoom : drawsBefore k < capacity)
    (statusBound : drawsBefore k + cost ≤ capacity)
    (drawBound : drawsBefore k + cost ≤ drawsBefore (k + 1))
    (room : k < budget) (roomPlan : k < plan.length)
    (compiles : (ValuePlan.compileRun language regions σ0 inputs.length plan).isSome = true)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sep : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (tableD : Separated (rowsFootprint spec.imageRows).byte D)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)}
    {X Ctx : NativeState → Prop} {Pay : NativeState → NativeState → Prop}
    (adapt : ∀ f, DefaultEntryMem.FiniteFetchCtx spec config rows mapping m X catalogue cost f → Ctx f)
    (tail : DefaultEntryMem.MemTailAt real spec config rows Ctx D w writes K x next us Pay cost)
    (xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay f g → Pay x g)
    (noVector : writes.vector = false)
    (nextPlaced : next = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x)
    (effectOf : ∀ fin, RegBind.Holds us x fin → Pay x fin → ValuePlan.Holds language view regions plan[k] x fin) :
    ∃ fin, modelStep real x = .ok () fin ∧
      Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
        language view regions σ0 inputs plan entry capacity drawsBefore (k + 1) fin ∧
      ValuePlan.Holds language view regions plan[k] x fin ∧ CurrentMTE2.BodyFrame D x fin := by
  have currentRows := bounded_rows entry x capacity (drawsBefore k) cost
    inv.statusRows inv.trace statusBound
  have hq : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.core.v1.quiet
  obtain ⟨fin,run,pins,quiet,current,pc,debug,features,gic,closed,_,bind,⟨written,frame,_,sub⟩,pay,_,sys,br,tco,tls,z,delta⟩ :=
    DefaultEntryMem.entry_mem_next_choice real spec config rows mapping w writes K x inv.core.v1.pins next
      (offset (k + 1)) us m X D Pay catalogue cost Ctx
      (fun fetched ctx fetchedChoice => adapt fetched ⟨ctx,
        rows_after_delta x fetched cost cost 0 currentRows fetchedChoice (by omega)⟩) tail inv.core.v1.gic inv.core.v1.features
      inv.core.v1.debug (budget - (k + 1)) hq base (offset k) inv.core.v1.pc page aligned nextPlaced
      inv.core.v1.current inv.core.closed scope image loadBase inv.core.placed sep codeD inv.core.raw
      inv.core.noUpd xferX xferPay inv.core.post inv.core.mode inv.core.controls
      (bounded_status entry x capacity (drawsBefore k) inv.statusRows inv.trace statusRoom)
      inv.core.debug inv.core.feat inv.core.dcache ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have wo := frame.mono sub
  have effect := effectOf fin bind pay
  exact ⟨fin,run,of_pair_effect inv roomPlan compiles ⟨pins,features,debug,current,quiet,gic,pc⟩
    closed sys br tco wo tableD codeD effect cost delta drawBound,effect,⟨wo,z noVector,tls⟩⟩

#print axioms mem_next_finite
end TranslateSpan.DefaultMTE2
