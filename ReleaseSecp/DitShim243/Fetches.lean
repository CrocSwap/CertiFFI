import DitShim243.Fetch
import DitShim243.StackClasses
import DefaultHeapShimControl
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ReleaseProfile
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace DitShim243.Fetches

def word (imm : BitVec 26) : Nat → BitVec 32
  | 0 => NativeEntryDispatch.BtiC.word
  | 1 => StackClasses.w1
  | 2 => NativeEntryDispatch.MrsDit.word 9#5
  | 3 => NativeEntryBodyDispatch.Stp.selected 9#5 30#5 0#7
  | 4 => NativeEntryDispatch.DitOn.word
  | 5 => NativeEntryDispatch.IsbSy.word
  | 6 => NativeEntryCallerDispatch.Bl.word imm
  | 7 => NativeEntryBodyDispatch.Ldp.selected 9#5 30#5 0#7
  | 8 => StackClasses.w8
  | 9 => NativeEntryDispatch.MsrDit.word 9#5
  | _ => EntryBodyRet.W 30#5

structure ShimFetchesInv (L : Nat) {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (base : BitVec 64)
    (offS : Nat → BitVec 64) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (start : Nat) (imm : BitVec 26) : Type where
  ob0 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget 0 catalogue x →
    FetchObligations spec config rows mapping (word imm 0) x
  ob1 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget 1 catalogue x →
    FetchObligations spec config rows mapping (word imm 1) x
  ob2 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget 2 catalogue x →
    FetchObligations spec config rows mapping (word imm 2) x
  ob3 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget 3 catalogue x →
    FetchObligations spec config rows mapping (word imm 3) x
  ob4 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget 4 catalogue x →
    FetchObligations spec config rows mapping (word imm 4) x
  ob5 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget 5 catalogue x →
    FetchObligations spec config rows mapping (word imm 5) x
  ob6 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget 6 catalogue x →
    FetchObligations spec config rows mapping (word imm 6) x
  ob365 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget (L + 8) catalogue x →
    FetchObligations spec config rows mapping (word imm 7) x
  ob8 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget (L + 9) catalogue x →
    FetchObligations spec config rows mapping (word imm 8) x
  ob9 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget (L + 10) catalogue x →
    FetchObligations spec config rows mapping (word imm 9) x
  ob10 : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offS budget (L + 11) catalogue x →
    FetchObligations spec config rows mapping (word imm 10) x

def of_static (L : Nat) {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (base : BitVec 64)
    (offS : Nat → BitVec 64) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (start : Nat) (imm : BitVec 26)
    (static : Fetch.CodeFacts spec mapping m scope image base start (word imm))
    (offPre : ∀ j, j ≤ 6 → offS j = Geometry.shimPC start j)
    (offPost : ∀ j, L + 8 ≤ j → j ≤ L + 11 → offS j = Geometry.shimPC start (j - (L + 1))) :
    ShimFetchesInv L spec config rows mapping m scope image base offS budget catalogue start imm := by
  refine { ob0 := ?_, ob1 := ?_, ob2 := ?_, ob3 := ?_, ob4 := ?_, ob5 := ?_, ob6 := ?_, ob365 := ?_, ob8 := ?_, ob9 := ?_, ob10 := ?_ }
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget 0 0
      catalogue (by decide) (offPre 0 (by omega)) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget 1 1
      catalogue (by decide) (offPre 1 (by omega)) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget 2 2
      catalogue (by decide) (offPre 2 (by omega)) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget 3 3
      catalogue (by decide) (offPre 3 (by omega)) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget 4 4
      catalogue (by decide) (offPre 4 (by omega)) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget 5 5
      catalogue (by decide) (offPre 5 (by omega)) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget 6 6
      catalogue (by decide) (offPre 6 (by omega)) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget (L + 8) 7
      catalogue (by decide) (by rw [offPost (L + 8) (by omega) (by omega), show (L + 8) - (L + 1) = 7 by omega]) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget (L + 9) 8
      catalogue (by decide) (by rw [offPost (L + 9) (by omega) (by omega), show (L + 9) - (L + 1) = 8 by omega]) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget (L + 10) 9
      catalogue (by decide) (by rw [offPost (L + 10) (by omega) (by omega), show (L + 10) - (L + 1) = 9 by omega]) x inv
  · intro x inv
    exact Fetch.fetch spec config rows mapping m scope image base start (word imm) static offS budget (L + 11) 10
      catalogue (by decide) (by rw [offPost (L + 11) (by omega) (by omega), show (L + 11) - (L + 1) = 10 by omega]) x inv

end DitShim243.Fetches
