-- Finite canonical representatives for exactly the native-selected query map.
import TranslateSpan.SelectedMap
import TranslateSpan.FiniteEntry
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.SelectedRepresentatives
open SelectedMap

def rawFor (readRaw writeRaw : AccessDescriptor) (write : Bool) : AccessDescriptor :=
  if write then writeRaw else readRaw

theorem raw_shape (readRaw writeRaw : AccessDescriptor)
    (readShape : DataShape false readRaw) (writeShape : DataShape true writeRaw) (write : Bool) :
    DataShape write (rawFor readRaw writeRaw write) := by
  cases write <;> assumption

def pairQueries (readRaw writeRaw : AccessDescriptor) (site : Site) : List AccessQuery :=
  let raw := rawFor readRaw writeRaw site.write
  match NativeAccess.PairGeometry.selected site.address with
  | .one16 => [⟨site.address,⟨raw,NativeAccess.Logical.accessAligned site.address 16 true⟩,16⟩]
  | .two8 => (List.finRange 2).map fun j => ⟨NativeAccess.PairSplit.halfAddress site.address j,⟨raw,true⟩,8⟩
  | .bytes => (List.finRange 16).map fun j => ⟨site.address + BitVec.ofNat 64 j.val,⟨raw,false⟩,1⟩

theorem pair_cover (readRaw writeRaw : AccessDescriptor)
    (readShape : DataShape false readRaw) (writeShape : DataShape true writeRaw)
    (site : Site) (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int)
    (permitted : pairPermitted site va acc aligned size) :
    ∃ q ∈ pairQueries readRaw writeRaw site,
      q.va = va ∧ q.size = size ∧ AccAgree q.request.raw acc := by
  obtain ⟨shape,actual⟩ := permitted
  have agree := (raw_shape readRaw writeRaw readShape writeShape site.write).agree shape
  cases chosen : NativeAccess.PairGeometry.selected site.address with
  | one16 =>
    rw [chosen] at actual
    obtain ⟨hva,_,hsize⟩ := actual
    subst va
    subst size
    refine ⟨⟨site.address,⟨rawFor readRaw writeRaw site.write,
      NativeAccess.Logical.accessAligned site.address 16 true⟩,16⟩,?_,rfl,rfl,agree⟩
    simp only [pairQueries,chosen,List.mem_singleton]
  | two8 =>
    rw [chosen] at actual
    obtain ⟨j,hva,_,hsize⟩ := actual
    subst va
    subst size
    refine ⟨⟨NativeAccess.PairSplit.halfAddress site.address j,
      ⟨rawFor readRaw writeRaw site.write,true⟩,8⟩,?_,rfl,rfl,agree⟩
    simp only [pairQueries,chosen]
    exact List.mem_map.mpr ⟨j,by simp,rfl⟩
  | bytes =>
    rw [chosen] at actual
    obtain ⟨j,hva,hsize⟩ := actual
    subst va
    subst size
    refine ⟨⟨site.address + BitVec.ofNat 64 j.val,
      ⟨rawFor readRaw writeRaw site.write,false⟩,1⟩,?_,rfl,rfl,agree⟩
    simp only [pairQueries,chosen]
    exact List.mem_map.mpr ⟨j,by simp,rfl⟩

def queries (readRaw writeRaw fetchRaw : AccessDescriptor) (sites : List Site)
    (code : List (BitVec 64)) : List AccessQuery :=
  code.map (fun va => ⟨va,⟨fetchRaw,true⟩,4⟩) ++ sites.flatMap (pairQueries readRaw writeRaw)

theorem query_cover (readRaw writeRaw fetchRaw : AccessDescriptor)
    (readShape : DataShape false readRaw) (writeShape : DataShape true writeRaw)
    (fetchShape : FetchShape fetchRaw) (sites : List Site) (code : List (BitVec 64))
    (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int)
    (member : SelectedMap.permitted sites code va acc aligned size) :
    ∃ q ∈ queries readRaw writeRaw fetchRaw sites code,
      q.va = va ∧ q.size = size ∧ AccAgree q.request.raw acc := by
  rcases member with ⟨inCode,shape,_,hsize⟩ | ⟨site,inSites,permitted⟩
  · subst size
    refine ⟨⟨va,⟨fetchRaw,true⟩,4⟩,?_,rfl,rfl,fetchShape.agree shape⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨va,inCode,rfl⟩)
  · obtain ⟨q,inq,hva,hsize,agree⟩ := pair_cover readRaw writeRaw readShape writeShape site va acc aligned size permitted
    exact ⟨q,List.mem_append_right _ (List.mem_flatMap.mpr ⟨site,inSites,inq⟩),hva,hsize,agree⟩

theorem pair_length (readRaw writeRaw : AccessDescriptor) (site : Site) :
    (pairQueries readRaw writeRaw site).length ≤ 16 := by
  cases chosen : NativeAccess.PairGeometry.selected site.address <;> simp [pairQueries,chosen]

theorem query_length (readRaw writeRaw fetchRaw : AccessDescriptor) (sites : List Site)
    (code : List (BitVec 64)) :
    (queries readRaw writeRaw fetchRaw sites code).length ≤ code.length + 16 * sites.length := by
  have dataBound : (sites.flatMap (pairQueries readRaw writeRaw)).length ≤ 16 * sites.length := by
    induction sites with
    | nil => simp
    | cons site rest ih =>
      have bound := pair_length readRaw writeRaw site
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  simp only [queries,List.length_append,List.length_map]
  omega

def slots {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (qs : List AccessQuery)
    (certificates : ∀ q ∈ qs, S1AccessData spec config rows q) : List (FiniteEntry.Slot spec config rows) :=
  qs.attach.map fun q => ⟨q.val,certificates q.val q.property⟩

theorem slots_length {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (qs : List AccessQuery)
    (certificates : ∀ q ∈ qs, S1AccessData spec config rows q) :
    (slots spec config rows qs certificates).length = qs.length := by simp [slots]

/-- Certificates/coverage are pure static data. The concrete program must build
these from pinned checked logical tables, rather than assume a native answer. -/
theorem slots_cover (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (readRaw writeRaw fetchRaw : AccessDescriptor)
    (readShape : DataShape false readRaw) (writeShape : DataShape true writeRaw)
    (fetchShape : FetchShape fetchRaw) (sites : List Site) (code : List (BitVec 64))
    (certificates : ∀ q ∈ queries readRaw writeRaw fetchRaw sites code, S1AccessData spec config rows q)
    (domains : ∀ q ∈ queries readRaw writeRaw fetchRaw sites code, domain q.va) :
    FiniteEntry.Covers spec config rows (consumerMap sites code mapping table)
      (slots spec config rows (queries readRaw writeRaw fetchRaw sites code) certificates) := by
  intro va acc aligned size permitted
  obtain ⟨q,member,hva,hsize,agree⟩ := query_cover readRaw writeRaw fetchRaw readShape writeShape fetchShape sites code va acc aligned size permitted
  refine ⟨?_,⟨q,certificates q member⟩,?_,hva,hsize,agree⟩
  · change domain va
    rw [← hva]
    exact domains q member
  · exact List.mem_map.mpr ⟨⟨q,member⟩,by simp,rfl⟩

#print axioms rawFor
#print axioms raw_shape
#print axioms pairQueries
#print axioms pair_cover
#print axioms queries
#print axioms query_cover
#print axioms pair_length
#print axioms query_length
#print axioms slots
#print axioms slots_length
#print axioms slots_cover
end TranslateSpan.SelectedRepresentatives
