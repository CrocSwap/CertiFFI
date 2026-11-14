import TranslateSpan.DefaultScalarTrace
import TranslateSpan.CurrentMemMTE2

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue ArmCertPipe NativeAccess NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.DefaultMTE2

theorem class_next_effect_frame (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (view : Physical.BytePA) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64))
    (language : ValuePlan.Language) (plan : List (ValuePlan.Step language))
    (profile : AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (entry : NativeState) (capacity : Nat) (drawsBefore : Nat → Nat) (D : Nat → Prop)
    (drawsNext : drawsBefore k ≤ drawsBefore (k + 1))
    (room : k < budget) (roomPlan : k < plan.length)
    (compiles : (ValuePlan.compileRun language regions σ0 inputs.length plan).isSome = true)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (next : NativeState → BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option VUpd))
    (fl : Option (VUpd × VUpd × VUpd × VUpd))
    (x : NativeState)
    (inv : Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
      language view regions σ0 inputs plan entry capacity drawsBefore k x)
    (tail : ClassTailXAt real w writes K x (next x) vus fl)
    (tailChoice : DefaultScalarTrace.TailChoiceAt real x w)
    (effectOf : ∀ fin, modelStep real x = .ok () fin →
      VHolds vus fl x fin → fin.mem = x.mem → ValuePlan.Holds language view regions plan[k] x fin)
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
        language view regions σ0 inputs plan entry capacity drawsBefore (k + 1) fin ∧
      ValuePlan.Holds language view regions plan[k] x fin ∧ CurrentMTE2.BodyFrame D x fin := by
  have hq : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.core.v1.quiet
  obtain ⟨fin,run,pins,quiet,current,pc,debug,features,gic,closed,placed,vh,memory,sys,_gcs,br,tco,z,tls⟩ :=
    ClassMTE2Frame.entry_class_next real spec config rows mapping w writes K x inv.core.v1.pins (next x)
      (offset (k + 1)) vus fl tail inv.core.v1.gic inv.core.v1.features
      inv.core.v1.debug (budget - (k + 1)) hq base (offset k) inv.core.v1.pc page aligned nextPlaced
      inv.core.v1.current m inv.core.closed scope image loadBase inv.core.placed separated
      inv.core.raw inv.core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have effect := effectOf fin run vh memory
  have agrees := ValuePlan.advance language view regions σ0 inputs plan k x fin roomPlan compiles inv.agrees effect
  have profileNext := CurrentMTE2.profile_of_sys sys inv.core.profileAt
  have delta := DefaultScalarTrace.step_choice real spec config rows mapping m scope image loadBase
    base offset budget profile catalogue k room page aligned w x fin inv.core ob tailChoice run
  obtain ⟨used, priorDelta, priorBound⟩ := inv.trace
  have trace : ∃ used, ChoiceDelta entry fin used ∧ used ≤ drawsBefore (k + 1) :=
    ⟨used, by simpa only [Nat.add_zero] using choice_delta_trans priorDelta delta,
      by omega⟩
  refine ⟨fin,run,⟨⟨⟨pins,features,debug,current,quiet,gic,pc⟩,closed,placed,?_,?_,
    CurrentMTE2.post_of_sys sys inv.core.post,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.core.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.core.debug,?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.core.dcache,profileNext,
    controls_of_sys inv.core.controls sys tco⟩,
    BranchMTE2.pins_step x fin inv.branch sys pins br,agrees,inv.statusRows,trace⟩,
    effect,⟨?_,z,tls⟩⟩
  · rw [memory]; exact inv.core.raw
  · intro wr acc shape
    rw [hostHAFT_eq sys]
    exact inv.core.noUpd wr acc shape
  · rw [sys.feat]
    exact inv.core.feat

  · intro address outside
    rw [memory]

theorem class_next_frame (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (view : Physical.BytePA) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64))
    (language : ValuePlan.Language) (plan : List (ValuePlan.Step language))
    (profile : AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (entry : NativeState) (capacity : Nat) (drawsBefore : Nat → Nat) (D : Nat → Prop)
    (drawsNext : drawsBefore k ≤ drawsBefore (k + 1))
    (room : k < budget) (roomPlan : k < plan.length)
    (compiles : (ValuePlan.compileRun language regions σ0 inputs.length plan).isSome = true)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (next : NativeState → BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option VUpd))
    (fl : Option (VUpd × VUpd × VUpd × VUpd))
    (planEntry : plan[k] = ValuePlan.legacy language ⟨vus,fl,[]⟩)
    (x : NativeState)
    (inv : Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
      language view regions σ0 inputs plan entry capacity drawsBefore k x)
    (tail : ClassTailXAt real w writes K x (next x) vus fl)
    (tailChoice : DefaultScalarTrace.TailChoiceAt real x w)
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
        language view regions σ0 inputs plan entry capacity drawsBefore (k + 1) fin ∧
      ValuePlan.Holds language view regions plan[k] x fin ∧ CurrentMTE2.BodyFrame D x fin := by
  apply class_next_effect_frame real spec config rows mapping m scope image loadBase separated
    base offset budget view regions σ0 inputs language plan profile catalogue k
    entry capacity drawsBefore D drawsNext room roomPlan compiles page aligned
    w writes K next vus fl x inv tail tailChoice
    (fun fin _ vh memory => ?_) nextPlaced ob
  rw [planEntry]
  exact (ValuePlan.holds_legacy language view regions ⟨vus,fl,[]⟩ x fin).mpr
    ⟨vh,Physical.memV_nil_of_mem view regions x fin memory⟩

#print axioms class_next_effect_frame
#print axioms class_next_frame
end TranslateSpan.DefaultMTE2
