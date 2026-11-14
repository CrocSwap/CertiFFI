import Bridge.CruxGenGuarded.ChainInvV3
import Bridge.CruxGenGuarded.E17BeforeFetch
import Bridge.CruxGenGuarded.ClosedChain
import ArmCertTranslateModel.HeapV2Initial
import ArmCertTranslateModel.PlanChecks
import ArmCertTranslateModel.ClosedTable
import ArmCertTranslateModel.C9InitialPlacement
import HeapV2StepCerts.RegBind
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.CodeData
import ArmCertWalk.NoUpdatePath

/-! H-P26: ChainInv v3 at index 0 for an ARBITRARY heap-v2 deployment (spec, config, rows, mapping,
base, pins, offset, consumer map), from primitive premise groups instead of an opaque `init3`:
* `EntryRegsOK`: register-only entry/host facts (all decidable on a concrete register file), including
  the pure current-S1 check `checkCurrentS1Pure` (whose checkImagePure conjunct also yields `raw`);
* the timer premise `HookQuiet budget x`, a separate budget-indexed argument of `init3_of` (E23 form);
* `EntryMemOK`: entry memory satisfies the entry plan (all code bytes at their mapped PAs, the table
  rows), the static code/table/permission coverage facts, and data presence;
* closed membership of the consumer map at the entry state (per-deployment closure check;
  `init3_of_represented` takes the RepresentedAt form).
HAND. -/

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
open ArmCert.Translate ArmCert.Translate.Model
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeInit3

/-- Register-only entry premises (host EL0 state at the deployment's entry). -/
structure EntryRegsOK {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (base : BitVec 64) (offset : Nat → BitVec 64) (p : HeapV2E17.Pins)
    (x : NativeState) : Prop where
  pins : StepPins x
  features : EntryActualFetch.EntryFeatures x.regs
  debug : E11Debug.E11CheckDebug x.regs
  gic : x.regs.bank_Option_InterruptID .__GIC_Pending = none
  pc : x.regs._PC = base + offset 0
  branch : Crypto.BranchV2.BranchPinsV2PA x
  sp : x.regs.SP_EL0 = BitVec.ofInt 64 ((p.sp : Nat) : Int)
  x0 : x.regs.gpr[(0 : Fin 31).val] = BitVec.ofInt 64 ((p.x0 : Nat) : Int)
  x1 : x.regs.gpr[(1 : Fin 31).val] = BitVec.ofInt 64 ((p.x1 : Nat) : Int)
  post2 : MemM1.MemReadD2.PostRegs2 x.regs
  mode : HostEL0ModeAt x.regs
  edebug : ExistingE11DebugAt x.regs
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  dcache : currentDCache x.regs = true
  checked : checkCurrentS1Pure spec config rows x.regs = true
  noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
    NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true

/-- Memory/loader premises at the entry state. -/
structure EntryMemOK {domain : QueryDomain} (spec : TopologyImageSpec domain) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (tableRows : NativeSourceInit.Plan)
    (p : HeapV2E17.Pins) (x : NativeState) : Prop where
  sat : NativeSourceInit.Satisfies (HeapV2.entryPlan base mapping HeapV2StepCerts.codeOffsets tableRows) x.mem
  codeMapped : ∀ o ∈ HeapV2StepCerts.codeOffsets, ∃ pa, mapping (MemReloc.imageAddress base o) = some pa
  codePresent : ∀ o ∈ HeapV2StepCerts.codeOffsets, ∃ byte, HeapV2.image base o = some byte
  tables : ∀ row ∈ imageRowsPlan spec.imageRows, row ∈ tableRows
  declared : PermissionRowsDeclared rows spec.imageRows
  present : HeapV2StepCerts.C3.DataPresent p mapping x

theorem placed_of {domain : QueryDomain} {spec : TopologyImageSpec domain} {rows : List PermissionRow}
    {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {tableRows : NativeSourceInit.Plan}
    {p : HeapV2E17.Pins} {x : NativeState} (M : EntryMemOK spec rows mapping base tableRows p x) :
    MemReloc.ImageOn HeapV2StepCerts.codeScope (HeapV2.image base) x base mapping := by
  intro offset scope
  obtain ⟨pa, hpa⟩ := M.codeMapped offset scope
  obtain ⟨byte, hb⟩ := M.codePresent offset scope
  have row : (pa, byte) ∈ HeapV2.entryPlan base mapping HeapV2StepCerts.codeOffsets tableRows :=
    List.mem_append_left _ (mem_imagePlan.2 ⟨offset, scope, hpa, hb⟩)
  exact ⟨byte, pa, hb, hpa, M.sat _ row⟩

theorem current_of {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64}
    {offset : Nat → BitVec 64} {tableRows : NativeSourceInit.Plan} {p : HeapV2E17.Pins} {x : NativeState}
    (R : EntryRegsOK spec config rows base offset p x) (M : EntryMemOK spec rows mapping base tableRows p x) :
    CurrentS1At spec config rows x :=
  current_s1_of_plan spec config rows x M.sat
    (fun row member => List.mem_append_right _ (M.tables row member)) M.declared R.checked

theorem raw_of {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64}
    {offset : Nat → BitVec 64} {tableRows : NativeSourceInit.Plan} {p : HeapV2E17.Pins} {x : NativeState}
    (R : EntryRegsOK spec config rows base offset p x) (M : EntryMemOK spec rows mapping base tableRows p x) :
    RawImageAt spec.imageRows x.mem := by
  have pure : checkImagePure spec.imageRows (spec.params.pie == 1#1) (spec.params.ha == 1#1)
      (spec.params.hd == 1#1) = true := by
    have c := R.checked
    simp only [checkCurrentS1Pure, Bool.and_eq_true] at c
    exact c.2.1
  exact raw_image_of_check _ _ _ _ _ ((checkImage_of_satisfies M.sat
    (fun row member => List.mem_append_right _ (M.tables row member))).trans pure)

/-- H-P26: the full ChainInv v3 at index 0 for an arbitrary deployment, from the primitive premises. -/
theorem init3_of {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {base : BitVec 64}
    {offset : Nat → BitVec 64} {tableRows : NativeSourceInit.Plan} {p : HeapV2E17.Pins} {x : NativeState}
    (R : EntryRegsOK spec config rows base offset p x) (M : EntryMemOK spec rows mapping base tableRows p x)
    (X : ClosedMembershipAt spec config rows mapping m x) (budget : Nat)
    (quiet : ArmCert.HookQuiet.V0.HookQuiet budget x) :
    ChainInvV3.ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope
      (HeapV2.image base) base base offset budget p 0 x := by
  refine
    { v2 := { v1 := { pins := R.pins
                      features := R.features
                      debug := R.debug
                      current := E17NonVacuity.before_fetch_of_current _ (current_of R M)
                      quiet := quiet
                      gic := R.gic
                      pc := R.pc }
              closed := ClosedChain.closed_before_fetch _ X
              placed := placed_of M
              branch := R.branch }
      regBind := HeapV2StepCerts.RegBind.initial R.sp
        (by simp only [HeapV2StepCerts.RegBind.regVal]; exact R.x0)
        (by simp only [HeapV2StepCerts.RegBind.regVal]; exact R.x1)
      present := M.present
      raw := raw_of R M
      noUpd := R.noUpd
      post2 := R.post2
      mode := R.mode
      debug := R.edebug
      feat := R.feat
      dcache := R.dcache }

/-- The same, from RepresentedAt (closed_of_represented). -/
theorem init3_of_represented {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {base : BitVec 64}
    {offset : Nat → BitVec 64} {tableRows : NativeSourceInit.Plan} {p : HeapV2E17.Pins} {x : NativeState}
    (R : EntryRegsOK spec config rows base offset p x) (M : EntryMemOK spec rows mapping base tableRows p x)
    (X : RepresentedAt spec config rows mapping m x) (budget : Nat)
    (quiet : ArmCert.HookQuiet.V0.HookQuiet budget x) :
    ChainInvV3.ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope
      (HeapV2.image base) base base offset budget p 0 x :=
  init3_of R M (closed_of_represented X) budget quiet

#print axioms placed_of
#print axioms current_of
#print axioms raw_of
#print axioms init3_of
#print axioms init3_of_represented
end NativeInit3
