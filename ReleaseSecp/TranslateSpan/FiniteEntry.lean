-- Private AUX producer: finite pure certificates checked at one declared entry.
import ArmCertTranslateModel.CurrentS1Checks
import ArmCertTranslateModel.ClosedTable
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.FiniteEntry

/-- Pure static logical-path/permission data. No state, frame, future run or
state-indexed proof field occurs in this carrier. -/
abbrev Slot {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) :=
  (query : AccessQuery) × S1AccessData spec config rows query

/-- A bounded list of existing scalar query checks at this entry only.
The final concrete profile must pin the exact cap/list/state/map and obtain
independent positive review; this definition grants no caller-leaf admission. -/
def checkRepresentatives {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (cap : Nat) (slots : List (Slot spec config rows)) (entry : ArmCertWalk.State) : Bool :=
  decide (slots.length ≤ cap) && slots.all
    (fun slot => checkCurrentS1Access spec config rows mapping slot.1 slot.2 entry)

/-- Coverage is static: each permitted query has the exact VA/size and an
agreeing descriptor in the finite list, and belongs to the actual domain. -/
def Covers {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (slots : List (Slot spec config rows)) : Prop :=
  ∀ va acc aligned size, consumer.permitted va acc aligned size →
    domain ⟨va,⟨acc,aligned⟩,size⟩ ∧
    ∃ slot ∈ slots, slot.1.va = va ∧ slot.1.size = size ∧ AccAgree slot.1.request.raw acc

theorem bounded {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {cap : Nat} {slots : List (Slot spec config rows)} {entry : ArmCertWalk.State}
    (checked : checkRepresentatives spec config rows mapping cap slots entry = true) :
    slots.length ≤ cap := by
  simp only [checkRepresentatives, Bool.and_eq_true] at checked
  exact of_decide_eq_true checked.1

theorem slot_current {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {cap : Nat} {slots : List (Slot spec config rows)} {entry : ArmCertWalk.State}
    (checked : checkRepresentatives spec config rows mapping cap slots entry = true)
    (slot : Slot spec config rows) (member : slot ∈ slots) :
    CurrentS1AccessAt spec config rows mapping slot.1 slot.2 entry := by
  simp only [checkRepresentatives, Bool.and_eq_true] at checked
  exact current_s1_access_of_check spec config rows mapping slot.1 slot.2 entry
    (List.all_eq_true.mp checked.2 slot member)

/-- This helper derives actual closed membership at the one checked entry.
It is not an assumption about a later call, stateAt index or run. The final
program must derive the pure certificates/coverage and bind the exact checked
entry/context to reviewed primitive leaves. -/
theorem closed_at_entry {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {cap : Nat} {slots : List (Slot spec config rows)} {entry : ArmCertWalk.State}
    (coverage : Covers spec config rows consumer slots)
    (checked : checkRepresentatives spec config rows mapping cap slots entry = true) :
    ClosedMembershipAt spec config rows mapping consumer entry := by
  intro va acc aligned size permitted
  obtain ⟨inDomain,slot,member,hva,hsize,agree⟩ := coverage va acc aligned size permitted
  have current := slot_current checked slot member
  rcases slot with ⟨⟨v,req,sz⟩,data⟩
  change v = va at hva
  change sz = size at hsize
  subst v
  subst sz
  exact ⟨⟨va,⟨acc,aligned⟩,size⟩,rfl,rfl,rfl,rfl,inDomain,
    S1AccessData.transfer (r' := ⟨acc,aligned⟩) data agree,
    CurrentS1AccessAt.transfer (r' := ⟨acc,aligned⟩) current agree⟩

#print axioms Slot
#print axioms checkRepresentatives
#print axioms Covers
#print axioms bounded
#print axioms slot_current
#print axioms closed_at_entry
end TranslateSpan.FiniteEntry
