import Bridge.CruxGenGuarded.ConsumerMapOn
import ArmCertTranslateModel.HeapV2ShimPlan
open Sail ArmFull
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmCert.Translate.Model.HeapV2E17
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

/-! a design decision shim + body consumer map (H-P13 item (1)). The shim runs at
base + 0x10548 and BLs the body; its only data access is the 16-byte saved pair (X9, X30) at
SP_shim − 16, which is the body's SP pin. The map permits the body's path-restricted accesses
(PermittedOn S), the shim's code fetches, and that one 16-byte slot (read or write). -/

/-- VA of the shim code word at shim-relative offset `offset` for load base `base`. -/
def shimCodeVA (base : Nat) (offset : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (base + HeapV2ShimPlan.shimOffset + offset)

def PermittedShim (S : Nat × Nat × Int × Nat × Bool → Prop) (p : Pins) (base : Nat) (va : BitVec 64)
    (acc : AccessDescriptor) (size : Int) : Prop :=
  PermittedOn S p base va acc size ∨
    (∃ code ∈ HeapV2ShimPlan.codeWords, va = shimCodeVA base code.1 ∧ size = 4 ∧ FetchShape acc) ∨
    (∃ w : Bool, va = BitVec.ofNat 64 p.sp ∧ size = 16 ∧ DataShape w acc)

def consumerMapShim (S : Nat × Nat × Int × Nat × Bool → Prop) (p : Pins) (base : Nat)
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  ⟨fun va => BitVec.ofNat 56 ((mapping va).getD 0), fun va acc _ size => PermittedShim S p base va acc size, table⟩

/-- The body's permitted accesses are shim-map accesses (a body state's closed membership at
the shim map implies it at consumerMapOn S, by restriction). -/
theorem permittedShim_of_on {S : Nat × Nat × Int × Nat × Bool → Prop} {p : Pins} {base : Nat}
    {va : BitVec 64} {acc : AccessDescriptor} {size : Int} (h : PermittedOn S p base va acc size) :
    PermittedShim S p base va acc size := Or.inl h

theorem consumerShim_agrees {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (S : Nat × Nat × Int × Nat × Bool → Prop) (p : Pins) (base : Nat) (mapping : BitVec 64 → Option Nat)
    (mapped : ∀ va acc size, PermittedShim S p base va acc size → ∃ pa, mapping va = some pa ∧ pa < 2 ^ 56) :
    ConsumerMapAgrees spec mapping (consumerMapShim S p base mapping (rowsFootprint spec.imageRows).byte) := by
  refine ⟨?_, fun _ inside => inside⟩
  intro va acc aligned size permitted
  obtain ⟨pa, hm, bound⟩ := mapped va acc size permitted
  simp only [consumerMapShim, hm, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

#print axioms consumerShim_agrees
end ArmCert.Translate.Model.HeapV2E17
