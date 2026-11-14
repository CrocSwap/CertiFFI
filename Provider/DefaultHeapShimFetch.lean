-- the shim's 11 fetch obligations in the invariant-indexed
-- form taken by TranslateShim.ReleaseV2Inv.shim_release_v2_inv, from ONE static deployment premise
-- (TranslateShim ShimCodeStatic, discharged by ShimDeploy.codeStatic_of_check) and the image/offset equations.
-- Each obligation is TranslateShim.ShimFetch.shimFetch at the shim word of that step (HeapV2ShimPlan.codeWords).
import DefaultHeapShimFetchBase
import NativeShimFetch.Inv
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
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapShimFetch
open NativeShimFetch (w1 w8 imm26 w1_word w8_word)
open ArmBridge.CruxGenGuarded.Release (shimPC shimMap)
structure ShimFetchesInv (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue) : Type where
  ob0 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 0 catalogue x →
    FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word x
  ob1 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 1 catalogue x →
    FetchObligations spec config rows mapping w1 x
  ob2 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 2 catalogue x →
    FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) x
  ob3 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 3 catalogue x →
    FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7) x
  ob4 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 4 catalogue x →
    FetchObligations spec config rows mapping NativeEntryDispatch.DitOn.word x
  ob5 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 5 catalogue x →
    FetchObligations spec config rows mapping NativeEntryDispatch.IsbSy.word x
  ob6 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 6 catalogue x →
    FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x
  ob365 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 365 catalogue x →
    FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7) x
  ob8 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 366 catalogue x →
    FetchObligations spec config rows mapping w8 x
  ob9 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 367 catalogue x →
    FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) x
  ob10 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 368 catalogue x →
    FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) x

/-- **Premise A from static deployment facts.** `static` is ShimCodeStatic (deployment check
    ShimDeploy.codeStatic_of_check); `himage`/`hload` say the run's image is the deployed heap-v2 image at `base`;
    `offPre`/`offPost` are release_heapv2's own offset premises. -/
def of_static (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (static : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC j) (offPost : ∀ j, 365 ≤ j → j ≤ 368 → offS j = shimPC (j - 358)) :
    ShimFetchesInv real spec config rows mapping pins scope image loadBase base offS budget catalogue := by
  subst image; subst loadBase
  have pre : ∀ j, j ≤ 6 → offS j = BitVec.ofNat 64 (0x10548 + 4 * j) := fun j hj => offPre j hj
  have post : ∀ j, 365 ≤ j → j ≤ 368 → offS j = BitVec.ofNat 64 (0x10548 + 4 * (j - 358)) := fun j h1 h2 => offPost j h1 h2
  exact
  { ob0 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 0 catalogue
      0x0 0xd503245f (by simp [HeapV2ShimPlan.codeWords]) (pre 0 (by decide)) _ (by first | rfl | decide) x inv
    ob1 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 1 catalogue
      0x4 0xd10043ff (by simp [HeapV2ShimPlan.codeWords]) (pre 1 (by decide)) _ w1_word x inv
    ob2 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 2 catalogue
      0x8 0xd53b42a9 (by simp [HeapV2ShimPlan.codeWords]) (pre 2 (by decide)) _ (by first | rfl | decide) x inv
    ob3 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 3 catalogue
      0xc 0xa9007be9 (by simp [HeapV2ShimPlan.codeWords]) (pre 3 (by decide)) _ (by first | rfl | decide) x inv
    ob4 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 4 catalogue
      0x10 0xd503415f (by simp [HeapV2ShimPlan.codeWords]) (pre 4 (by decide)) _ (by first | rfl | decide) x inv
    ob5 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 5 catalogue
      0x14 0xd5033fdf (by simp [HeapV2ShimPlan.codeWords]) (pre 5 (by decide)) _ (by first | rfl | decide) x inv
    ob6 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 6 catalogue
      0x18 0x97ffff46 (by simp [HeapV2ShimPlan.codeWords]) (pre 6 (by decide)) _ (by first | rfl | decide) x inv
    ob365 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 365 catalogue
      0x1c 0xa9407be9 (by simp [HeapV2ShimPlan.codeWords]) (post 365 (by decide) (by decide)) _ (by first | rfl | decide) x inv
    ob8 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 366 catalogue
      0x20 0x910043ff (by simp [HeapV2ShimPlan.codeWords]) (post 366 (by decide) (by decide)) _ w8_word x inv
    ob9 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 367 catalogue
      0x24 0xd51b42a9 (by simp [HeapV2ShimPlan.codeWords]) (post 367 (by decide) (by decide)) _ (by first | rfl | decide) x inv
    ob10 := fun x inv => DefaultHeapShimFetchBase.shimFetch spec config rows mapping (fun _ => True) pins _ base scope static offS budget 368 catalogue
      0x28 0xd65f03c0 (by simp [HeapV2ShimPlan.codeWords]) (post 368 (by decide) (by decide)) _ (by first | rfl | decide) x inv }

#print axioms of_static

end ReleaseProfile.DefaultHeapShimFetch
