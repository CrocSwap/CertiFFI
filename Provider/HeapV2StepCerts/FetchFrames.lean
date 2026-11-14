-- Memory: memory facts across the ACTUAL fetch and across class steps for ChainInv v3.
-- Inputs: native_fetch_current_preserving's `clean` (CleanTranslateResultFields from fetchPre (beforeFetchState x))
-- and final.mem = translated.mem — the same style as Carry.placed_fetch.
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.RawFetch
import ArmCertTranslateModel.StoreDomain
import ArmCertTranslateModel.StoreHistory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.FetchFrames
open ArmCertWalk ArmBridge.Draft

/-- F1: the fetch translation writes only table bytes. -/
theorem fetch_mem_frame {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {x : NativeState} {translated final : ArmCertWalk.State} {result : FaultRecord × AddressDescriptor}
    (clean : CleanTranslateResultFields spec config rows mapping query leafLevel view
      (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)) result translated)
    (finalMem : final.mem = translated.mem) :
    WritesOnly (rowsFootprint spec.imageRows).byte
      (fun a => (ArmBridge.CruxGenGuarded.beforeFetchState x).mem[a]?) (fun a => final.mem[a]?) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, history, _⟩ := clean
  have h := history.frame rfl
  intro a ha
  rw [finalMem]
  exact h a ha

/-- Byte presence is kept by the fetch translation (stores write Some bytes). -/
theorem fetch_isSome {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {x : NativeState} {translated final : ArmCertWalk.State} {result : FaultRecord × AddressDescriptor}
    (clean : CleanTranslateResultFields spec config rows mapping query leafLevel view
      (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)) result translated)
    (finalMem : final.mem = translated.mem) (a : Nat) :
    (final.mem[a]?).isSome = (x.mem[a]?).isSome := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, history, _⟩ := clean
  rw [finalMem]
  exact history.byte_presence a

/-- F3: DataPresent across the fetch. -/
theorem present_fetch {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {x : NativeState} {translated final : ArmCertWalk.State} {result : FaultRecord × AddressDescriptor}
    {p : HeapV2E17.Pins} {dmap : BitVec 64 → Option Nat}
    (clean : CleanTranslateResultFields spec config rows mapping query leafLevel view
      (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)) result translated)
    (finalMem : final.mem = translated.mem) (h : C3.DataPresent p dmap x) : C3.DataPresent p dmap final :=
  C3.DataPresent.carry (fun a ha => by rw [fetch_isSome clean finalMem a]; exact ha) h

/-- Across a NON-memory class step (fin.mem = fetched.mem). -/
theorem present_class {p : HeapV2E17.Pins} {dmap : BitVec 64 → Option Nat} {fetched fin : NativeState}
    (mem : fin.mem = fetched.mem) (h : C3.DataPresent p dmap fetched) : C3.DataPresent p dmap fin :=
  C3.DataPresent.carry (fun a ha => by rw [mem]; exact ha) h

theorem raw_class {rows : List ImageRow} {fetched fin : NativeState} (mem : fin.mem = fetched.mem)
    (h : RawImageAt rows fetched.mem) : RawImageAt rows fin.mem := RawFetch.raw_mem_eq h mem

/-- Across a MEMORY class step: mem_tailD_<K>'s presence conjunct and WritesOnly / Separated conjuncts. -/
theorem present_mem {p : HeapV2E17.Pins} {dmap : BitVec 64 → Option Nat} {fetched fin : NativeState}
    (keep : ∀ a : Nat, (fetched.mem[a]?).isSome → (fin.mem[a]?).isSome) (h : C3.DataPresent p dmap fetched) :
    C3.DataPresent p dmap fin := C3.DataPresent.carry keep h

theorem raw_mem {rows : List ImageRow} {written : Nat → Prop} {fetched fin : NativeState}
    (wo : WritesOnly written (fun a => fetched.mem[a]?) (fun a => fin.mem[a]?))
    (sep : Separated (rowsFootprint rows).byte written) (h : RawImageAt rows fetched.mem) : RawImageAt rows fin.mem :=
  RawFetch.raw_writes h wo sep

#print axioms fetch_mem_frame
#print axioms present_fetch
#print axioms present_class
#print axioms raw_mem
end HeapV2StepCerts.FetchFrames
