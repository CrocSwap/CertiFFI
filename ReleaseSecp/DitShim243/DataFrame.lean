import DitShim243.Initial
import DitShim243.Pre
import TranslateSpan.DefaultBudget
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan TranslateSpan.SecpRawDeployment ArmCertValue ArmCertPipe HeapV2StepCerts NativeMteTagCheck ReleaseProfile
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace DitShim243.DataFrame

def sources (p : Plan) : List Region := p.buffers.map Prod.fst ++ p.outputs.map Prod.fst ++ p.regions.map Prod.fst

def safePin (i : Nat) : Bool := decide (i < 31 ∧ i ≠ 9 ∧ i ≠ 30)

def checkPins (p : Plan) : Bool :=
  (sources p ++ (sources p).map p.normalize).all (fun r => safePin r.pin) && p.accesses.all (fun a => safePin a.pin)

theorem buffer_member (p : Plan) (r : Region) (n : Nat) (member : (r,n) ∈ p.buffers) : r ∈ sources p := by
  simp only [sources,List.mem_append]
  exact Or.inl (Or.inl (List.mem_map.mpr ⟨(r,n),member,rfl⟩))

theorem output_member (p : Plan) (r : Region) (n : Nat) (member : (r,n) ∈ p.outputs) : r ∈ sources p := by
  simp only [sources,List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨(r,n),member,rfl⟩))

theorem region_member (p : Plan) (r : Region) (n : Nat) (member : (r,n) ∈ p.regions) : r ∈ sources p := by
  simp only [sources,List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨(r,n),member,rfl⟩)

theorem pin_safe (p : Plan) (checked : checkPins p = true) (r : Region) (member : r ∈ sources p) :
    r.pin < 31 ∧ r.pin ≠ 9 ∧ r.pin ≠ 30 := by
  simp only [checkPins,Bool.and_eq_true] at checked
  exact of_decide_eq_true (List.all_eq_true.mp checked.1 r (List.mem_append_left _ member))

theorem normalized_safe (p : Plan) (checked : checkPins p = true) (r : Region) (member : r ∈ sources p) :
    (p.normalize r).pin < 31 ∧ (p.normalize r).pin ≠ 9 ∧ (p.normalize r).pin ≠ 30 := by
  simp only [checkPins,Bool.and_eq_true] at checked
  exact of_decide_eq_true (List.all_eq_true.mp checked.1 (p.normalize r)
    (List.mem_append_right _ (List.mem_map.mpr ⟨r,member,rfl⟩)))

section Prefix
variable (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (start : Nat)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase base : BitVec 64)
    (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (capacity : Nat) (e : NativeState)
    (pre : Pre.ShimPreMG real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e)
include pre

theorem gpr (i : Nat) (small : i < 31) (n9 : i ≠ 9) (n30 : i ≠ 30) :
    entryGPR (stateAt real e 7) i = entryGPR e i := by
  have kept := pre.keepPre ⟨i,small⟩ n9 n30
  simpa only [entryGPR,dif_pos small] using kept

theorem region (p : Plan) (checked : checkPins p = true) (r : Region) (member : r ∈ sources p) (j : Nat) :
    regionVA (stateAt real e 7) r j = regionVA e r j := by
  obtain ⟨small,n9,n30⟩ := pin_safe p checked r member
  unfold regionVA
  rw [gpr real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e pre r.pin small n9 n30]

theorem view (p : Plan) (checked : checkPins p = true) (r : Region) (member : r ∈ sources p) (j : Nat) :
    SecpRawDeployment.view p mapping (stateAt real e 7) r j = SecpRawDeployment.view p mapping e r j := by
  obtain ⟨small,n9,n30⟩ := normalized_safe p checked r member
  unfold SecpRawDeployment.view regionVA
  rw [gpr real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e pre (p.normalize r).pin small n9 n30]

theorem present (a : Nat) (old : (e.mem[a]?).isSome = true) : ((stateAt real e 7).mem[a]?).isSome = true := by
  classical
  by_cases inside : RtShim2.ShimMem.slotBytes pins mapping a
  · obtain ⟨n,mapped,lower,upper⟩ := inside
    have stored := pre.slot4 n mapped (a-n) (by omega)
    rw [show n + (a-n) = a by omega] at stored
    rw [pre.mem47 a,stored]
    rfl
  · rw [pre.memPre a inside]
    exact old

end Prefix

/-- Generic source-location lemma, copied without any historical run instance. -/
theorem memBL_member : ∀ (rs : List (Region × Nat)) (base : Nat) (g : Region) (j i k : Nat),
    memBL rs base g j = some (i,k) → ∃ n, (g,n) ∈ rs ∧ j < n := by
  intro rs
  induction rs with
  | nil => intro base g j i k h; simp [memBL] at h
  | cons p tail ih =>
    obtain ⟨r,n⟩ := p
    intro base g j i k h
    simp only [memBL] at h
    split at h
    · next test => obtain ⟨rfl,hj⟩ := test; exact ⟨n,List.mem_cons_self ..,hj⟩
    · obtain ⟨n',hm,hj⟩ := ih (base+n) g j i k h
      exact ⟨n',List.mem_cons_of_mem _ hm,hj⟩

theorem profile_current {catalogue : ControlCatalogue} {s : NativeState}
    (controls : DefaultAt catalogue s) (lse2 : s.regs.FeatureImpl[111] = true)
    (alignment : _get_SCTLR_EL2_Type_A catalogue.sctlrEL2 = 0#1) : NativeAccess.ProfileAt (profile s) s := by
  refine ⟨lse2,rfl,⟨controls.host.el,controls.host.nrw,controls.host.aa64,controls.host.rme,
    controls.host.vhe,controls.host.ns,controls.host.e2h,controls.host.tge⟩,?_⟩
  rw [controls.preparation.2.1]
  exact alignment

#print axioms gpr
#print axioms region
#print axioms view
#print axioms present
#print axioms profile_current
end DitShim243.DataFrame
