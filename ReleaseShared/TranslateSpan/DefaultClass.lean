import TranslateSpan.DefaultCurrent
import TranslateSpan.CurrentClass

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue ArmCertPipe NativeAccess NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.DefaultMTE2

theorem controls_of_sys {s t : NativeState} {catalogue : ControlCatalogue}
    (controls : DefaultAt catalogue s) (sys : SysEq2 s.regs t.regs)
    (tco : t.regs.PSTATE.TCO = s.regs.PSTATE.TCO) : DefaultAt catalogue t := by
  refine ⟨⟨sys.el ▸ controls.host.el,sys.nrw ▸ controls.host.nrw,
    sys.feat ▸ controls.host.aa64,sys.feat ▸ controls.host.rme,
    sys.feat ▸ controls.host.vhe,sys.scr ▸ controls.host.ns,
    sys.hcr ▸ controls.host.e2h,sys.hcr ▸ controls.host.tge⟩,
    tco.trans controls.tco,sys.sctlr ▸ controls.tcf0,?_⟩
  obtain ⟨tcr,sctlr,hcr,scr⟩ := controls.preparation
  exact ⟨sys.tcr.trans tcr,sys.sctlr.trans sctlr,sys.hcr.trans hcr,sys.scr.trans scr⟩

theorem class_next (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (view : Physical.BytePA) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64))
    (language : ValuePlan.Language) (plan : List (ValuePlan.Step language))
    (profile : AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (roomPlan : k < plan.length)
    (compiles : (ValuePlan.compileRun language regions σ0 inputs.length plan).isSome = true)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (next : NativeState → BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option VUpd))
    (fl : Option (VUpd × VUpd × VUpd × VUpd))
    (planEntry : plan[k] = ValuePlan.legacy language ⟨vus,fl,[]⟩)
    (x : NativeState)
    (core : Core spec config rows mapping m scope image loadBase base offset budget profile catalogue k x)
    (branch : BranchMTE2.Pins x)
    (agreement : ValuePlan.AgreesAt language view regions σ0 inputs plan k x)
    (tail : ClassTailXAt real w writes K x (next x) vus fl)
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      Core spec config rows mapping m scope image loadBase base offset budget profile catalogue (k + 1) fin ∧
      BranchMTE2.Pins fin ∧
      ValuePlan.AgreesAt language view regions σ0 inputs plan (k + 1) fin ∧
      ValuePlan.Holds language view regions plan[k] x fin := by
  have hq : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin,run,pins,quiet,current,pc,debug,features,gic,closed,placed,vh,memory,sys,_gcs,br,tco⟩ :=
    ClassMTE2.entry_class_next real spec config rows mapping w writes K x core.v1.pins (next x)
      (offset (k + 1)) vus fl tail core.v1.gic core.v1.features
      core.v1.debug (budget - (k + 1)) hq base (offset k) core.v1.pc page aligned nextPlaced
      core.v1.current m core.closed scope image loadBase core.placed separated
      core.raw core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have effect : ValuePlan.Holds language view regions plan[k] x fin := by
    rw [planEntry]
    exact (ValuePlan.holds_legacy language view regions ⟨vus,fl,[]⟩ x fin).mpr
      ⟨vh,Physical.memV_nil_of_mem view regions x fin memory⟩
  have agrees := ValuePlan.advance language view regions σ0 inputs plan k x fin roomPlan compiles agreement effect
  have profileNext := CurrentMTE2.profile_of_sys sys core.profileAt
  refine ⟨fin,run,⟨⟨pins,features,debug,current,quiet,gic,pc⟩,closed,placed,?_,?_,
    CurrentMTE2.post_of_sys sys core.post,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr core.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde core.debug,?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr core.dcache,profileNext,
    controls_of_sys core.controls sys tco⟩,
    BranchMTE2.pins_step x fin branch sys pins br,agrees,effect⟩
  · rw [memory]; exact core.raw
  · intro wr acc shape
    rw [hostHAFT_eq sys]
    exact core.noUpd wr acc shape
  · rw [sys.feat]
    exact core.feat

#print axioms controls_of_sys
#print axioms class_next
end TranslateSpan.DefaultMTE2
