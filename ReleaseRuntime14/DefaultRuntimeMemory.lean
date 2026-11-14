-- Finite initial oracle rows and trace advancement for actual Runtime14 steps.
import DefaultRuntimeCurrent
import DefaultMemRoute

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultRuntime

section
variable {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget : Nat} {extra : Nat → NativeState → Prop} {catalogue : NativeMteTagCheck.ControlCatalogue}
    {entry x fin : NativeState} {capacity k cost : Nat} {past : Nat → Nat}

#check "CURRENT_DECL current_status"
theorem current_status
    (inv : InvG spec config rows mapping m scope image loadBase base offset budget extra catalogue entry capacity past k x)
    (room : past k < capacity) : NativeMteTagCheck.TagStatusOK x :=
  TranslateSpan.DefaultMTE2.bounded_status entry x capacity (past k) inv.statusRows inv.trace room

#check "CURRENT_DECL advance"
theorem InvG.advance
    (inv : InvG spec config rows mapping m scope image loadBase base offset budget extra catalogue entry capacity past k x)
    (core : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin)
    (nextExtra : extra (k + 1) fin)
    (choice : ∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ cost)
    (bound : past k + cost ≤ past (k + 1)) :
    InvG spec config rows mapping m scope image loadBase base offset budget extra catalogue entry capacity past (k + 1) fin := by
  obtain ⟨used, prefixChoice, prefixBound⟩ := inv.trace
  obtain ⟨draws, stepChoice, stepBound⟩ := choice
  exact ⟨core, nextExtra, inv.statusRows,
    ⟨used + draws, NativeMteTagCheck.choice_delta_trans prefixChoice stepChoice, by omega⟩⟩

#check "CURRENT_DECL current_at_offset"
theorem current_at_offset {offset' : Nat → BitVec 64}
    (same : offset' k = offset k)
    (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x) :
    DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset' budget k catalogue x := by
  exact ⟨⟨inv.v1.pins, inv.v1.features, inv.v1.debug, inv.v1.current, inv.v1.quiet,
      inv.v1.gic, by rw [same]; exact inv.v1.pc⟩, inv.closed, inv.placed, inv.branch,
    inv.raw, inv.noUpd, inv.post, inv.mode, inv.debug, inv.feat, inv.dcache, inv.controls⟩

end
#print axioms current_at_offset
#print axioms current_status
#print axioms InvG.advance
end ReleaseProfile.DefaultRuntime
