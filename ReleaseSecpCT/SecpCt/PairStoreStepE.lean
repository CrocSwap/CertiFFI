-- secp CT0: STP side: event version of Xlate's DefaultPairSelected.stp_tailG (dispatch one16/two8/bytes by the
-- public VA alignment) over the generated STP event tails, and of DefaultSelectedPairFacts.stp_step (via mem_next_finiteE).
import TranslateSpan.CurrentMemMTE2
import TranslateSpan.DefaultEntryMem
import TranslateSpan.DefaultFiniteMem
import TranslateSpan.DefaultFiniteRows
import TranslateSpan.DefaultPairJoin
import TranslateSpan.DefaultPairSelected
import TranslateSpan.SelectedStoreFacts
import SecpCt.MemE
import SecpCt.PairSelectedE
import SecpCt.PairStoreTailE
import SecpCt.PairStepE
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

namespace SecpCt.PairRecs
/-- The request (VA, size) list of the actual STP path at A (selected by A's alignment: public). -/
def stpVAS (A : BitVec 64) : List (BitVec 64 × Nat) :=
  match NativeAccess.PairGeometry.selected A with
  | .one16 => oneVAS A
  | .two8 => splitVAS A
  | .bytes => bytesVAS A
end SecpCt.PairRecs

namespace TranslateSpan.CtE.DefaultPairSelected
variable {catalogue : NativeMteTagCheck.ControlCatalogue}
open TranslateSpan.DefaultPairSelected
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts ArmCertMemPipe
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv
open NativeAccess
open NativeAccess.LdpBytes NativeAccess.PairGeometry

theorem stp_tailE (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : PairDefault236.Current.Consumer) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (D : Nat → Prop)
    (source : NativeState) (profile : AccessProfile) (pins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows (PairDefault236.Ctx spec config rows mapping m catalogue
      (TranslateSpan.DefaultBudget.cost (pairAddr source Rn imm7)) (StoreFacts domain spec mapping m D imm7 Rn)) D
      (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) {} 617 source (source.regs._PC + 4#64)
      []
      (fun f g => StorePay mapping Rt Rt2 imm7 Rn f g ∧ ArmCertMemPipe.EvD spec (SecpCt.PairRecs.vaRecs spec true (SecpCt.PairRecs.stpVAS (pairAddr f Rn imm7))) f g)
      (TranslateSpan.DefaultBudget.cost (pairAddr source Rn imm7)) := by
  intro fetched enc0 budget stepPins input guard quiet it ss current ctx
  let sel := NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7
  have dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) 617 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Stp8.dispatch_at real pc Rt Rn Rt2 imm7 t (by simpa using see)
  have noEret := stp8_noEret Rt Rn Rt2 imm7
  have addr : pairAddr fetched Rn imm7 = pairAddr source Rn imm7 := by
    simp only [pairAddr, ← input.gpr]
  have statusRows := ctx.statusRows
  rw [← addr] at statusRows
  unfold TranslateSpan.DefaultBudget.cost at statusRows
  have geom := selected_spec (pairAddr fetched Rn imm7)
  have facts := ctx.prog
  simp only [StoreFacts] at facts
  generalize choice : selected (pairAddr fetched Rn imm7) = c at geom facts statusRows
  cases c with
  | one16 =>
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 1 (PairDefault236.PairStoreTail.OneFacts spec mapping m D imm7 Rn) fetched :=
      ⟨ctx.current,⟨geom,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.CtE.PairStoreTail.stp_one_tailE real domain spec config rows mapping m sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret D source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [StorePay,TranslateSpan.DefaultBudget.cost,← addr,choice,SecpCt.PairRecs.stpVAS,PairDefault236.PairStoreTail.OnePay,PairDefault236.PairStoreTail.SplitPay,PairDefault236.PairStoreTail.BytePay] using run
  | two8 =>
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 2 (PairDefault236.PairStoreTail.SplitFacts spec mapping m D imm7 Rn) fetched :=
      ⟨ctx.current,⟨geom.1,geom.2,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.CtE.PairStoreTail.stp_split_tailE real domain spec config rows mapping m sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret D source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [StorePay,TranslateSpan.DefaultBudget.cost,← addr,choice,SecpCt.PairRecs.stpVAS,PairDefault236.PairStoreTail.OnePay,PairDefault236.PairStoreTail.SplitPay,PairDefault236.PairStoreTail.BytePay] using run
  | bytes =>
    have not8 : (pairAddr fetched Rn imm7).toNat % 8 ≠ 0 := by
      intro h
      by_cases h16 : (pairAddr fetched Rn imm7).toNat % 16 = 0
      · simp [selected,h16] at choice
      · simp [selected,h16,h] at choice
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 16 (PairDefault236.PairStoreTail.ByteFacts domain spec mapping m D imm7 Rn) fetched :=
      ⟨ctx.current,⟨not8,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.CtE.PairStoreTail.stp_bytes_tailE real domain spec config rows mapping m sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret D source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [StorePay,TranslateSpan.DefaultBudget.cost,← addr,choice,SecpCt.PairRecs.stpVAS,PairDefault236.PairStoreTail.OnePay,PairDefault236.PairStoreTail.SplitPay,PairDefault236.PairStoreTail.BytePay] using run

end TranslateSpan.CtE.DefaultPairSelected
#print axioms TranslateSpan.CtE.DefaultPairSelected.stp_tailE

namespace TranslateSpan.DefaultSelectedPairFacts
open TranslateSpan.SelectedLoadFacts TranslateSpan.SelectedStoreFacts PairGeometry

theorem stp_stepE (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
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
    (facts : DefaultPairSelected.StoreFacts domain spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (r : Region) (word : Nat) (binding : DefaultPairSelected.Binding view r word mapping imm7 Rn x)
    (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words)
    (injective : Physical.RegionsInjective view regions)
    (vus : List (RegBind.Reg × Option VUpd))
    (compat : StepVCore.Compat vus [])
    (planEntry : plan[k] = ArmCertPipe.ValuePlan.legacy language ⟨vus,none,
      [.store (.x (RegBind.rk Rt)) r word,.store (.x (RegBind.rk Rt2)) r (word + 1)]⟩)
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      StepEvents.EvShape spec mapping (SecpCt.PairRecs.vaRecs spec true (SecpCt.PairRecs.stpVAS (pairAddr x Rn imm7))) x fin := by
  have effectOf (fin : NativeState) (holds : RegBind.Holds [] x fin)
      (pay : DefaultPairSelected.StorePay mapping Rt Rt2 imm7 Rn x fin) :
      ArmCertPipe.ValuePlan.Holds language view regions plan[k] x fin := by
    rw [planEntry]
    apply (ArmCertPipe.ValuePlan.holds_legacy language view regions _ x fin).mpr
    exact ⟨StepVCore.vholds_of_holds compat rfl holds
      (DefaultPairSelected.store_flags mapping Rt Rt2 imm7 Rn x fin pay),
      DefaultPairSelected.store_value view regions x fin r word mapping imm7 Rn Rt Rt2
        member fits injective binding pay⟩
  exact TranslateSpan.DefaultMTE2.mem_next_finiteE real inv statusRoom statusBound drawBound room roomPlan compiles page aligned separated
    tableD codeD
    (fun _ c => PairDefault236.Ctx.of_finite c)
    (fun f => SecpCt.PairRecs.vaRecs spec true (SecpCt.PairRecs.stpVAS (pairAddr f Rn imm7)))
    (fun f hg _ => by simp only [pairAddr, hg])
    nodup
    (TranslateSpan.CtE.DefaultPairSelected.stp_tailE real domain spec config rows mapping m imm7 Rn Rt Rt2 hRn hRt hRt2
      D x profile inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts domain spec mapping m D imm7 Rn g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping Rt Rt2 imm7 Rn g sp mm nz pay)
    rfl nextPlaced obligations effectOf


end TranslateSpan.DefaultSelectedPairFacts
#print axioms TranslateSpan.DefaultSelectedPairFacts.stp_stepE
