-- entry agreement conversion only where a concrete view-equality certificate is proved.
import ArmCertPipe.PhysicalDeploy
import ArmCertValue.ReleaseGen
set_option autoImplicit false
namespace ArmCertPipe.Physical
open ArmCertValue
open ArmCertValue.Physical (BytePA)
open ArmBridge.Draft
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk

private theorem memBL_location : ∀ (rs : List (Region × Nat)) (base : Nat) (g : Region) (j i k : Nat),
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

theorem view_eq_of_inputs {bytePA : BytePA} {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat}
    {rs : List (Region × Nat)}
    (view : rs.all (fun r => (List.range r.2).all (fun j =>
      bytePA r.1 j == mapping (BitVec.ofInt 64 ((pinv r.1.pin : Int)+r.1.off+j)))) = true)
    {g : Region} {j i k : Nat} (h : (σ0L rs).memB g j = some (i,k)) :
    bytePA g j = mapping (BitVec.ofInt 64 ((pinv g.pin : Int)+g.off+j)) := by
  obtain ⟨n,hm,hj⟩ := memBL_location rs 0 g j i k h
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 view (g,n) hm) j (List.mem_range.2 hj))

theorem zero_of_legacy {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {bytePA : BytePA}
    {regions : List Region} {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List StepV} {x : NativeState}
    (h : ArmCertPipe.AgreesAt mapping pinv regions σ0 inputs plan 0 x)
    (view : ∀ r j i k, σ0.memB r j = some (i,k) →
      bytePA r j = mapping (BitVec.ofInt 64 ((pinv r.pin : Int)+r.off+j))) :
    AgreesAt bytePA regions σ0 inputs plan 0 x := by
  obtain ⟨ds,σ,hc,ha,hb⟩ := h
  simp only [List.take_zero,compileRun,Option.some.injEq,Prod.mk.injEq] at hc
  obtain ⟨rfl,rfl⟩ := hc
  simp only [extend,List.foldl_nil] at ha hb
  apply agreesAt_zero (hB := hb)
  refine ⟨ha.1,ha.2.1,?_⟩
  intro r j i k hmb
  show (bytePA r j).bind _ = _
  rw [view r j i k hmb]
  exact ha.2.2 r j i k hmb

theorem replaceExtra {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase : MemReloc.Word} {base : BitVec 64} {offset : Nat → BitVec 64}
    {budget : Nat} {extra extra' : Nat → NativeState → Prop} {k : Nat} {x : NativeState}
    (h : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (hx : extra' k x) :
    ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra' k x :=
  ⟨h.v2,h.raw,h.noUpd,h.post2,h.mode,h.debug,h.feat,h.dcache,hx⟩

#print axioms zero_of_legacy
#print axioms view_eq_of_inputs
#print axioms replaceExtra
end ArmCertPipe.Physical
