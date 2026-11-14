import DitShim243.Fetches
import DitShim243.SlotMem
import TranslateSpan.SecpDefaultEntry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan TranslateSpan.SecpRawDeployment NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.Deployment

def shimCode (start : Nat) (imm : BitVec 26) : List (Nat × Nat) :=
  (List.range 11).map (fun j => (start + 4 * j, (Fetches.word imm j).toNat))

def extend (p : Plan) (start : Nat) (imm : BitVec 26) : Plan :=
  { p with code := p.code ++ shimCode start imm }

def allSites (p : Plan) (entry : NativeState) (slot : BitVec 64) : List SelectedMap.Site :=
  sites p entry ++ [⟨slot,false⟩,⟨slot,true⟩]

def consumer (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (start : Nat) (imm : BitVec 26) (slot : BitVec 64) :
    ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  SelectedMap.consumerMap (allSites p entry slot) (codeVAs (extend p start imm) base)
    mapping (rowsFootprint raw.imageRows).byte

def selectedQueries (p : Plan) (base : BitVec 64) (entry : NativeState)
    (start : Nat) (imm : BitVec 26) (slot : BitVec 64) : List AccessQuery :=
  SelectedRepresentatives.queries (QueryDescriptors.data false) (QueryDescriptors.data true)
    QueryDescriptors.fetch (allSites p entry slot) (codeVAs (extend p start imm) base)

def queries (p : Plan) (base : BitVec 64) (entry : NativeState)
    (start : Nat) (imm : BitVec 26) (slot : BitVec 64) : List AccessQuery :=
  selectedQueries p base entry start imm slot ++ bufferQueries p entry

def addresses (p : Plan) (base : BitVec 64) (entry : NativeState)
    (start : Nat) (imm : BitVec 26) (slot : BitVec 64) : List (BitVec 64) :=
  (queries p base entry start imm slot).map (·.va)

theorem shim_member (start : Nat) (imm : BitVec 26) (j : Nat) (bound : j < 11) :
    (start + 4 * j,(Fetches.word imm j).toNat) ∈ shimCode start imm :=
  List.mem_map.mpr ⟨j,List.mem_range.mpr bound,rfl⟩

theorem raw_subset (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (start : Nat) (imm : BitVec 26) (slot : BitVec 64)
    (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int)
    (permitted : (SecpRawDeployment.consumer p raw mapping base entry).permitted va acc aligned size) :
    (consumer p raw mapping base entry start imm slot).permitted va acc aligned size := by
  rcases permitted with fetch | ⟨site,member,access⟩
  · refine Or.inl ⟨?_,fetch.2⟩
    simpa only [codeVAs,extend,List.map_append] using
      (List.mem_append_left ((shimCode start imm).map (fun c => MemReloc.imageAddress base c.1)) fetch.1)
  · exact Or.inr ⟨site,List.mem_append_left _ member,access⟩

theorem code_permitted (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (start : Nat) (imm : BitVec 26) (slot : BitVec 64)
    (j : Nat) (bound : j < 11) (acc : AccessDescriptor) (shape : FetchShape acc) :
    (consumer p raw mapping base entry start imm slot).permitted (base + Geometry.shimPC start j) acc true 4 := by
  apply SelectedMap.fetch_member
  · exact List.mem_map.mpr ⟨(start + 4 * j,(Fetches.word imm j).toNat),
      List.mem_append_right _ (shim_member start imm j bound),rfl⟩
  · exact shape

theorem slot_permitted (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (start : Nat) (imm : BitVec 26) (pins : HeapV2E17.Pins)
    (aligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0) :
    SlotMem.SlotPerm (consumer p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp)) pins := by
  intro write acc shape
  let slot := BitVec.ofNat 64 pins.sp
  have member : (⟨slot,write⟩ : SelectedMap.Site) ∈ allSites p entry slot := by
    cases write <;> simp [allSites]
  have selected : PairGeometry.selected slot = .one16 := by
    simp only [PairGeometry.selected,slot,if_pos aligned]
  have natural : slot.toNat % 8 = 0 := by dsimp [slot]; omega
  have flag : Logical.accessAligned slot 16 true = true := by
    change IsAligned__1 slot (8 : Int) = true
    exact MemM1.MemReadD.isAligned8 slot natural
  have permitted := SelectedMap.one_member (allSites p entry slot) (codeVAs (extend p start imm) base)
    mapping (rowsFootprint raw.imageRows).byte ⟨slot,write⟩ member selected acc shape
  rw [flag] at permitted
  exact permitted

#print axioms raw_subset
#print axioms code_permitted
#print axioms slot_permitted
end DitShim243.Deployment
