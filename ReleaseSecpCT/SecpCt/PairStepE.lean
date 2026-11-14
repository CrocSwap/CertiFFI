-- secp CT0: event versions of Xlate's DefaultMTE2.mem_next_finite and DefaultSelectedPairFacts.ldp_step,
-- added to the same namespaces (distinct names) so every name resolves as in Xlate's originals.
import TranslateSpan.CurrentMemMTE2
import TranslateSpan.DefaultEntryMem
import TranslateSpan.DefaultFiniteMem
import TranslateSpan.DefaultFiniteRows
import TranslateSpan.DefaultPairJoin
import TranslateSpan.DefaultPairSelected
import TranslateSpan.SelectedStoreFacts
import SecpCt.MemE
import SecpCt.PairSelectedE
import TranslateSpan.DefaultSelectedPairFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue ArmCertPipe ArmCertMemPipe HeapV2StepCerts NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCertValue ArmCertMemPipe HeapV2StepCerts NativeAccess NativeAccess.LdpBytes
set_option maxHeartbeats 400000

namespace TranslateSpan.DefaultMTE2


theorem mem_next_finiteE (real : Type) [Sail.SailReal real]
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
    (dataOf : NativeState → List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (xferData : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → dataOf f = dataOf x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (tail : DefaultEntryMem.MemTailAt real spec config rows Ctx D w writes K x next us (fun f g => Pay f g ∧ ArmCertMemPipe.EvD spec (dataOf f) f g) cost)
    (xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay f g → Pay x g)
    (noVector : writes.vector = false)
    (nextPlaced : next = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x)
    (effectOf : ∀ fin, RegBind.Holds us x fin → Pay x fin → ValuePlan.Holds language view regions plan[k] x fin) :
    ∃ fin, modelStep real x = .ok () fin ∧ StepEvents.EvShape spec mapping (dataOf x) x fin := by
  have currentRows := bounded_rows entry x capacity (drawsBefore k) cost
    inv.statusRows inv.trace statusBound
  have hq : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.core.v1.quiet
  exact SecpCt.mem_ev real spec config rows mapping w writes K x inv.core.v1.pins next
      (offset (k + 1)) us m X D Pay catalogue cost Ctx
      (fun fetched ctx fetchedChoice => adapt fetched ⟨ctx,
        rows_after_delta x fetched cost cost 0 currentRows fetchedChoice (by omega)⟩) dataOf xferData nodup tail inv.core.v1.gic inv.core.v1.features
      inv.core.v1.debug (budget - (k + 1)) hq base (offset k) inv.core.v1.pc page aligned nextPlaced
      inv.core.v1.current inv.core.closed scope image loadBase inv.core.placed sep codeD inv.core.raw
      inv.core.noUpd xferX xferPay inv.core.post inv.core.mode inv.core.controls
      (bounded_status entry x capacity (drawsBefore k) inv.statusRows inv.trace statusRoom)
      inv.core.debug inv.core.feat inv.core.dcache ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code


#print axioms TranslateSpan.DefaultMTE2.mem_next_finiteE
end TranslateSpan.DefaultMTE2

namespace TranslateSpan.DefaultSelectedPairFacts
open TranslateSpan.SelectedLoadFacts TranslateSpan.SelectedStoreFacts PairGeometry

theorem ldp_stepE (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (view : Physical.BytePA) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64))
    (language : ArmCertPipe.ValuePlan.Language) (plan : List (ArmCertPipe.ValuePlan.Step language))
    (profile : AccessProfile) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (capacity : Nat) (drawsBefore : Nat → Nat) (x : NativeState)
    (inv : DefaultMTE2.Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue language view regions σ0 inputs plan entry capacity drawsBefore k x)
    (statusRoom : drawsBefore k < capacity)
    (statusBound : drawsBefore k + DefaultBudget.cost (pairAddr x Rn imm7) ≤ capacity)
    (drawBound : drawsBefore k + DefaultBudget.cost (pairAddr x Rn imm7) ≤ drawsBefore (k + 1))
    (roomPlan : k < plan.length)
    (compiles : (ArmCertPipe.ValuePlan.compileRun language regions σ0 inputs.length plan).isSome = true)
    (D : Nat → Prop) (tableD : Separated (rowsFootprint spec.imageRows).byte D)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (facts : DefaultPairSelected.LoadFacts domain mapping m imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (r : Region) (word : Nat) (binding : DefaultPairSelected.Binding view r word mapping imm7 Rn x)
    (vus : List (RegBind.Reg × Option VUpd))
    (compat : StepVCore.Compat vus [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)])
    (planEntry : plan[k] = ArmCertPipe.ValuePlan.legacy language ⟨vus,none,
      [.load (.x (RegBind.rk Rt)) r word,.load (.x (RegBind.rk Rt2)) r (word + 1)]⟩)
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      StepEvents.EvShape spec mapping (SecpCt.PairRecs.vaRecs spec false (SecpCt.PairRecs.ldpVAS (pairAddr x Rn imm7))) x fin := by
  have effectOf (fin : NativeState) (holds : RegBind.Holds [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] x fin)
      (pay : DefaultPairSelected.LoadPay mapping Rt Rt2 imm7 Rn x fin) :
      ArmCertPipe.ValuePlan.Holds language view regions plan[k] x fin := by
    rw [planEntry]
    apply (ArmCertPipe.ValuePlan.holds_legacy language view regions _ x fin).mpr
    exact ⟨StepVCore.vholds_of_holds compat rfl holds
      (DefaultPairSelected.load_flags mapping Rt Rt2 imm7 Rn x fin pay),
      DefaultPairSelected.load_value view regions x fin r word mapping imm7 Rn Rt Rt2
        hRt hRt2 hRtt binding pay⟩
  exact TranslateSpan.DefaultMTE2.mem_next_finiteE real inv statusRoom statusBound drawBound room roomPlan compiles page aligned separated
    (fun _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ c => PairDefault236.Ctx.of_finite c)
    (fun f => SecpCt.PairRecs.vaRecs spec false (SecpCt.PairRecs.ldpVAS (pairAddr f Rn imm7)))
    (fun f hg _ => by simp only [pairAddr, hg])
    nodup
    (TranslateSpan.CtE.DefaultPairSelected.ldp_tailE real domain spec config rows mapping m imm7 Rn Rt Rt2 hRn hRt hRt2
      hRtt x profile inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts domain mapping m imm7 Rn g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping Rt Rt2 imm7 Rn g sp mm nz pay)
    rfl nextPlaced obligations effectOf


#print axioms TranslateSpan.DefaultSelectedPairFacts.ldp_stepE
end TranslateSpan.DefaultSelectedPairFacts
