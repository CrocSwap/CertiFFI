-- the shim's 11 fetch obligations in the invariant-indexed
-- form taken by TranslateShim.ReleaseV2Inv.shim_release_v2_inv, from ONE static deployment premise
-- (TranslateShim ShimCodeStatic, discharged by ShimDeploy.codeStatic_of_check) and the image/offset equations.
-- Each obligation is TranslateShim.ShimFetch.shimFetch at the shim word of that step (HeapV2ShimPlan.codeWords).
import TranslateShim.ShimFetch
import Bridge.CruxGenGuarded.ReleaseHeadline
import NativeEntryDispatch.BtiC
import NativeEntryDispatch.MrsDit
import NativeEntryDispatch.DitOn
import NativeEntryDispatch.IsbSy
import NativeEntryDispatch.MsrDit
import NativeEntryBodyDispatch.Stp
import NativeEntryBodyDispatch.Ldp
import NativeEntryBodyDispatch.SubSp64
import NativeEntryBodyDispatch.AddSpRestore
import NativeEntryCallerDispatch.Bl
import Bridge.CruxGenGuarded.EntryBodyRet
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
namespace NativeShimFetch
open ArmBridge.CruxGenGuarded.Release (shimPC shimMap)

/-- The shim words of steps 1 (sub sp, #16) and 366 (add sp, #16) and the BL immediate of step 6. -/
def w1 : BitVec 32 := NativeEntryBodyDispatch.SubSp64.selected 16#12
def w8 : BitVec 32 := NativeEntryBodyDispatch.AddSpRestore.selected 16#12
theorem w1_word : w1 = BitVec.ofNat 32 0xd10043ff := by decide
theorem w8_word : w8 = BitVec.ofNat 32 0x910043ff := by decide
def imm26 : BitVec 26 := 0x3ffff46#26

/-- The invariant-indexed shim fetch obligations, field for field the ob' premises of shim_release_v2_inv. -/
structure ShimFetchesInv (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) : Type where
  ob0 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 0 x →
    FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word x
  ob1 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 1 x →
    FetchObligations spec config rows mapping w1 x
  ob2 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 2 x →
    FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) x
  ob3 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 3 x →
    FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7) x
  ob4 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 4 x →
    FetchObligations spec config rows mapping NativeEntryDispatch.DitOn.word x
  ob5 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 5 x →
    FetchObligations spec config rows mapping NativeEntryDispatch.IsbSy.word x
  ob6 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 6 x →
    FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x
  ob365 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 365 x →
    FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7) x
  ob8 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 366 x →
    FetchObligations spec config rows mapping w8 x
  ob9 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 367 x →
    FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) x
  ob10 : ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 368 x →
    FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) x

/-- **Premise A from static deployment facts.** `static` is ShimCodeStatic (deployment check
    ShimDeploy.codeStatic_of_check); `himage`/`hload` say the run's image is the deployed heap-v2 image at `base`;
    `offPre`/`offPost` are release_heapv2's own offset premises. -/
def of_static (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat)
    (static : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC j) (offPost : ∀ j, 365 ≤ j → j ≤ 368 → offS j = shimPC (j - 358)) :
    ShimFetchesInv real spec config rows mapping pins scope image loadBase base offS budget := by
  subst image; subst loadBase
  have pre : ∀ j, j ≤ 6 → offS j = BitVec.ofNat 64 (0x10548 + 4 * j) := fun j hj => offPre j hj
  have post : ∀ j, 365 ≤ j → j ≤ 368 → offS j = BitVec.ofNat 64 (0x10548 + 4 * (j - 358)) := fun j h1 h2 => offPost j h1 h2
  exact
  { ob0 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 0
      0x0 0xd503245f (by simp [HeapV2ShimPlan.codeWords]) (pre 0 (by decide)) _ (by first | rfl | decide) x inv
    ob1 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 1
      0x4 0xd10043ff (by simp [HeapV2ShimPlan.codeWords]) (pre 1 (by decide)) _ w1_word x inv
    ob2 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 2
      0x8 0xd53b42a9 (by simp [HeapV2ShimPlan.codeWords]) (pre 2 (by decide)) _ (by first | rfl | decide) x inv
    ob3 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 3
      0xc 0xa9007be9 (by simp [HeapV2ShimPlan.codeWords]) (pre 3 (by decide)) _ (by first | rfl | decide) x inv
    ob4 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 4
      0x10 0xd503415f (by simp [HeapV2ShimPlan.codeWords]) (pre 4 (by decide)) _ (by first | rfl | decide) x inv
    ob5 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 5
      0x14 0xd5033fdf (by simp [HeapV2ShimPlan.codeWords]) (pre 5 (by decide)) _ (by first | rfl | decide) x inv
    ob6 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 6
      0x18 0x97ffff46 (by simp [HeapV2ShimPlan.codeWords]) (pre 6 (by decide)) _ (by first | rfl | decide) x inv
    ob365 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 365
      0x1c 0xa9407be9 (by simp [HeapV2ShimPlan.codeWords]) (post 365 (by decide) (by decide)) _ (by first | rfl | decide) x inv
    ob8 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 366
      0x20 0x910043ff (by simp [HeapV2ShimPlan.codeWords]) (post 366 (by decide) (by decide)) _ w8_word x inv
    ob9 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 367
      0x24 0xd51b42a9 (by simp [HeapV2ShimPlan.codeWords]) (post 367 (by decide) (by decide)) _ (by first | rfl | decide) x inv
    ob10 := fun x inv => RtDit.ShimFetch.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 368
      0x28 0xd65f03c0 (by simp [HeapV2ShimPlan.codeWords]) (post 368 (by decide) (by decide)) _ (by first | rfl | decide) x inv }

#print axioms of_static
end NativeShimFetch
