import DitShim243.TopologyTransport
import DefaultCurrent
import TranslateSpan.CurrentMemMTE2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open ReleaseProfile TranslateSpan NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.CurrentBridge
open CheckedTopology

theorem to_raw (raw : Raw) (a b : List (BitVec 64)) (fuel : Nat)
    (ha : check raw a fuel = true) (hb : check raw b fuel = true)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (outer inner : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (outerScope innerScope : Nat → Prop) (image : MemReloc.Image) (loadBase base : BitVec 64)
    (outerOffset innerOffset : Nat → BitVec 64) (outerBudget innerBudget outerK innerK : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (profile : AccessProfile) (s : NativeState)
    (c : DefaultCurrent.CurrentInv (spec raw a fuel ha) config rows mapping outer outerScope image loadBase
      base outerOffset outerBudget outerK catalogue s)
    (samePC : outerOffset outerK = innerOffset innerK)
    (room : innerBudget - innerK ≤ outerBudget - outerK)
    (scopeSubset : ∀ o, innerScope o → outerScope o)
    (subset : ∀ va acc aligned size, inner.permitted va acc aligned size → outer.permitted va acc aligned size)
    (domain : ∀ va acc aligned size, inner.permitted va acc aligned size → va ∈ b)
    (profileAt : ProfileAt profile s) :
    DefaultMTE2.Core (spec raw b fuel hb) config rows mapping inner innerScope image loadBase base
      innerOffset innerBudget profile catalogue innerK s := by
  have current := TopologyTransport.current raw a b fuel ha hb config rows (beforeFetchState s) c.v1.current
  have closed := TopologyTransport.closed raw a b fuel ha hb config rows mapping outer inner
    (beforeFetchState s) subset domain c.closed
  have placed : MemReloc.ImageOn innerScope image s loadBase mapping := fun o inside => c.placed o (scopeSubset o inside)
  exact ⟨⟨c.v1.pins,c.v1.features,c.v1.debug,current,
      ArmCert.HookQuiet.V0.hookQuiet_mono room c.v1.quiet,c.v1.gic,c.v1.pc.trans (congrArg (base + ·) samePC)⟩,
    closed,placed,c.raw,c.noUpd,c.post,c.mode,c.debug,c.feat,c.dcache,profileAt,c.controls⟩

/-- Restore the broader shim context from the reached raw-body invariant.
Closed membership and placement are separately derived from the actual body
control-vector and write frames, not from an assumed successor execution. -/
theorem from_raw (raw : Raw) (a b : List (BitVec 64)) (fuel : Nat)
    (ha : check raw a fuel = true) (hb : check raw b fuel = true)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (outer inner : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (outerScope innerScope : Nat → Prop) (image : MemReloc.Image) (loadBase base : BitVec 64)
    (outerOffset innerOffset : Nat → BitVec 64) (outerBudget innerBudget outerK innerK : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (profile : AccessProfile) (s : NativeState)
    (c : DefaultMTE2.Core (spec raw b fuel hb) config rows mapping inner innerScope image loadBase
      base innerOffset innerBudget profile catalogue innerK s)
    (samePC : innerOffset innerK = outerOffset outerK)
    (room : outerBudget - outerK ≤ innerBudget - innerK)
    (branch : BranchMTE2.Pins s)
    (closed : ClosedMembershipAt (spec raw a fuel ha) config rows mapping outer (beforeFetchState s))
    (placed : MemReloc.ImageOn outerScope image s loadBase mapping) :
    DefaultCurrent.CurrentInv (spec raw a fuel ha) config rows mapping outer outerScope image loadBase
      base outerOffset outerBudget outerK catalogue s := by
  have current := TopologyTransport.current raw b a fuel hb ha config rows (beforeFetchState s) c.v1.current
  exact ⟨⟨c.v1.pins,c.v1.features,c.v1.debug,current,
      ArmCert.HookQuiet.V0.hookQuiet_mono room c.v1.quiet,c.v1.gic,c.v1.pc.trans (congrArg (base + ·) samePC)⟩,
    closed,placed,branch,c.raw,c.noUpd,c.post,c.mode,c.debug,c.feat,c.dcache,c.controls⟩

theorem of_core {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (scope : Nat → Prop)
    (image : MemReloc.Image) (loadBase base : BitVec 64) (off : Nat → BitVec 64)
    (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue) (profile : AccessProfile) (s : NativeState)
    (c : DefaultMTE2.Core spec config rows mapping m scope image loadBase base off budget profile catalogue k s)
    (branch : BranchMTE2.Pins s) :
    DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base off budget k catalogue s :=
  ⟨c.v1,c.closed,c.placed,branch,c.raw,c.noUpd,c.post,c.mode,c.debug,c.feat,c.dcache,c.controls⟩

theorem expand (raw : Raw) (a b : List (BitVec 64)) (fuel : Nat)
    (ha : check raw a fuel = true) (hb : check raw b fuel = true)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (outer inner : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (outerScope innerScope : Nat → Prop) (image : MemReloc.Image) (loadBase base : BitVec 64)
    (off : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue) (s : NativeState)
    (c : DefaultCurrent.CurrentInv (spec raw b fuel hb) config rows mapping inner innerScope image loadBase
      base off budget k catalogue s)
    (closed : ClosedMembershipAt (spec raw a fuel ha) config rows mapping outer (beforeFetchState s))
    (placed : MemReloc.ImageOn outerScope image s loadBase mapping) :
    DefaultCurrent.CurrentInv (spec raw a fuel ha) config rows mapping outer outerScope image loadBase
      base off budget k catalogue s := by
  exact ⟨⟨c.v1.pins,c.v1.features,c.v1.debug,
    TopologyTransport.current raw b a fuel hb ha config rows (beforeFetchState s) c.v1.current,
    c.v1.quiet,c.v1.gic,c.v1.pc⟩,closed,placed,c.branch,c.raw,c.noUpd,c.post,c.mode,c.debug,c.feat,c.dcache,c.controls⟩

theorem placed_frame (scope : Nat → Prop) (image : MemReloc.Image) (base : BitVec 64)
    (mapping : BitVec 64 → Option Nat) (output : Nat → Prop) (before after : NativeState)
    (old : MemReloc.ImageOn scope image before base mapping)
    (separated : ImageTableSeparated scope base mapping output)
    (frame : CurrentMTE2.BodyFrame output before after) :
    MemReloc.ImageOn scope image after base mapping := by
  intro o inside
  obtain ⟨byte,pa,hi,hm,hb⟩ := old o inside
  exact ⟨byte,pa,hi,hm,(frame.writes pa (separated o pa inside hm)).trans hb⟩

#print axioms of_core
#print axioms expand
#print axioms placed_frame
#print axioms to_raw
#print axioms from_raw
end DitShim243.CurrentBridge
