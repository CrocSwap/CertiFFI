import TranslateSpan.DefaultContext
import TranslateSpan.BranchMTE2
import ArmCertPipe.ValuePlan

open Sail ArmFull ArmCertWalk ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded ArmCertValue ArmCertPipe NativeAccess
open NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace TranslateSpan.DefaultMTE2

structure Inv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : AccessProfile) (catalogue : ControlCatalogue)
    (language : ValuePlan.Language) (view : Physical.BytePA) (regions : List Region)
    (initial : Sym) (inputs : List (BitVec 64)) (plan : List (ValuePlan.Step language))
    (entry : NativeState) (capacity : Nat) (drawsBefore : Nat → Nat)
    (k : Nat) (s : NativeState) : Prop where
  core : Core spec config rows mapping consumer scope image loadBase base offset budget
    profile catalogue k s
  branch : BranchMTE2.Pins s
  agrees : ValuePlan.AgreesAt language view regions initial inputs plan k s
  statusRows : NativeMteTagCheck.TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity
  trace : ∃ used, ChoiceDelta entry s used ∧ used ≤ drawsBefore k

theorem bounded_status (entry current : NativeState) (capacity limit : Nat)
    (rows : NativeMteTagCheck.TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity)
    (trace : ∃ used, ChoiceDelta entry current used ∧ used ≤ limit)
    (room : limit < capacity) : TagStatusOK current := by
  obtain ⟨used, delta, bound⟩ := trace
  exact tag_status_of_rows entry current _ capacity used rows delta.1 delta.2 (by omega)

theorem bounded_trace_next (entry current next : NativeState) (before after cost : Nat)
    (trace : ∃ used, ChoiceDelta entry current used ∧ used ≤ before)
    (step : ∃ draws, ChoiceDelta current next draws ∧ draws ≤ cost)
    (room : before + cost ≤ after) :
    ∃ used, ChoiceDelta entry next used ∧ used ≤ after := by
  obtain ⟨used, priorDelta, priorBound⟩ := trace
  obtain ⟨draws, delta, bound⟩ := step
  exact ⟨used + draws, choice_delta_trans priorDelta delta, by omega⟩

#print axioms bounded_status
#print axioms bounded_trace_next
end TranslateSpan.DefaultMTE2
