import TranslateMem.WalkInjSlot
import HeapV2StepCerts.E17General.Base

/-! Producers of the walk premises of functional_heapv2 (,: catalogued rows only).
* `leaf_of_closed`: closed membership (E17 (1a)) at any state gives, at every VA its consumer map permits, a stage-1
  leaf output address: `CurrentS1AccessAt.map.mapped` is `mapping va = leafOutputAddress va level view.stable`, which
  is `leafPA va` of the leaf read off the descriptor (level, leafBase, contiguous bit 52).
* `accessLeaf_of_dp`: AccessLeaf from the deployment's body-entry chain invariant (dp.init3, closed membership of the
  plan's consumer map at body entry, which permits every declared data access).
* `slotLeaf_of_closed`: SlotLeaf from any closed membership whose consumer map permits an access at the slot VA
  (the shim chain's, at its STP/LDP state).
* `input_present_of_dp`: the 32 input bytes are mapped and present at body entry (dp.init3.present on the 32 LDRB
  accesses at x1 + j). Stated with Release.bufByte's body (`(mapping (ofNat (x1 + j))).bind fun pa => s.mem[pa]?`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateMem
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCertValue ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft

/-- A closed-membership fact gives a leaf output address at every permitted VA. -/
theorem leaf_of_closed {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {s : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping m s) {va : BitVec 64} {acc : AccessDescriptor}
    {aligned : Bool} {size : Int} (perm : m.permitted va acc aligned size) :
    ∃ l : Leaf, mapping va = some (leafPA va l) := by
  obtain ⟨q, hva, -, -, -, -, data, cur⟩ := closed va acc aligned size perm
  let fa : FullAddress := { paspace := .PAS_NonSecure, address := S1LogicalReference.leafBase data.leafLevel data.view.stable }
  refine ⟨(data.leafLevel, fa, data.view.stable.getLsbD 52), ?_⟩
  rw [← hva, cur.map.mapped]; rfl

/-- The canonical EL0 GPR data descriptor of a read (false) / write (true). -/
def dataAcc (w : Bool) : AccessDescriptor :=
  { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := !w, write := w }

theorem dataAcc_shape (w : Bool) : DataShape w (dataAcc w) := by
  constructor <;> rfl

/-- **AccessLeaf** from the deployment premises (body-entry closed membership). -/
theorem accessLeaf_of_dp {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {pins : HeapV2E17.Pins}
    {entry : NativeState} {budget : Nat}
    (dp : HeapV2StepCerts.E17General.DeploymentPremises spec config rows mapping base pins entry budget) :
    AccessLeaf pins mapping := by
  intro e he
  exact leaf_of_closed dp.init3.v2.closed (acc := dataAcc e.2.2.2.2) (aligned := true)
    (size := (e.2.2.2.1 : Int)) (Or.inl ⟨e, he, rfl, rfl, dataAcc_shape _⟩)

/-- **SlotLeaf** from any closed membership whose consumer map permits an access at the slot VA. -/
theorem slotLeaf_of_closed {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {s : ArmCertWalk.State} (p : HeapV2E17.Pins)
    (closed : ClosedMembershipAt spec config rows mapping m s) {acc : AccessDescriptor} {aligned : Bool} {size : Int}
    (perm : m.permitted (BitVec.ofNat 64 p.sp) acc aligned size) : SlotLeaf p mapping :=
  leaf_of_closed closed perm

/-- Every input byte offset j < 32 is a declared 1-byte access on pin 2 (x1). -/
theorem input_accesses : (List.range 32).all (fun j =>
    HeapV2Plan.symbolicAccesses.any (fun e => e.2.1 == 2 && e.2.2.1 == (j : Int) && e.2.2.2.1 == 1)) = true := by
  decide

/-- **Input presence** at body entry: each input byte is mapped and present (Release.bufByte's body). -/
theorem input_present_of_dp {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {pins : HeapV2E17.Pins}
    {entry : NativeState} {budget : Nat}
    (dp : HeapV2StepCerts.E17General.DeploymentPremises spec config rows mapping base pins entry budget) :
    ∀ j, j < 32 → ∃ b, ((mapping (BitVec.ofNat 64 (pins.x1 + j))).bind fun pa => entry.mem[pa]?) = some b := by
  intro j hj
  obtain ⟨e, he, hc⟩ := List.any_eq_true.1 (List.all_eq_true.1 input_accesses j (List.mem_range.2 hj))
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hpin, hoff⟩, hsz⟩ := hc
  have hva : HeapV2E17.dataVA pins e = BitVec.ofNat 64 (pins.x1 + j) := by
    obtain ⟨k, pn, off, size, w⟩ := e
    simp only at hpin hoff; subst hpin hoff
    apply BitVec.eq_of_toNat_eq
    simp [HeapV2E17.dataVA, HeapV2E17.pin, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  obtain ⟨l, hl⟩ := accessLeaf_of_dp dp e he
  rw [hva] at hl
  have pres := dp.init3.present e he _ (by rw [hva]; exact hl) 0 (by omega)
  rw [Nat.add_zero] at pres
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 pres
  exact ⟨b, by rw [hl]; simpa using hb⟩

#print axioms leaf_of_closed
#print axioms accessLeaf_of_dp
#print axioms slotLeaf_of_closed
#print axioms input_present_of_dp
end TranslateMem
