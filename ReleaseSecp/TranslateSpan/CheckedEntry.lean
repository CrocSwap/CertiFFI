-- Executable bounded checks at one declared entry generate all access data internally.
import TranslateSpan.StaticData
import TranslateSpan.SelectedRepresentatives
import ArmCertTranslateModel.CurrentS1Checks
open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 4096
namespace TranslateSpan.CheckedEntry

/-- Existing scalar current checks read the leaf level/view directly from the
pure reference walk. No noncomputable certificate is evaluated by this Bool. -/
def checkCurrentFromWalk {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (mapping : BitVec 64 → Option Nat) (q : AccessQuery)
    (fuel : Nat) (entry : ArmCertWalk.State) : Bool :=
  match walkPath spec.logicalRows (effectiveBits spec.physicalConfig).toNat q.va fuel spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root with
  | some (.leaf level _ _ view) =>
      checkCurrentLayout spec.layout spec.params q.va entry.regs &&
      (checkTranslateQuery entry.regs spec.params q.va q.request.raw &&
      (decide (currentWalkEPD entry.regs q.va = 0#1) &&
      (checkLeafMap mapping spec.physicalConfig entry.regs q level view &&
        checkOutputCache q.request.raw entry.regs)))
  | _ => false

theorem current_of_checks {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (q : AccessQuery) (fuel : Nat) (entry : ArmCertWalk.State)
    (declared : StaticData.checkData spec config rows q fuel = true)
    (checked : checkCurrentFromWalk spec config mapping q fuel entry = true) :
    ∃ data : S1AccessData spec config rows q, CurrentS1AccessAt spec config rows mapping q data entry := by
  have checks := declared
  simp only [StaticData.checkData,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨⟨lower,accessEL,nonsecure⟩,found⟩ := checks
  unfold checkCurrentFromWalk at checked
  cases walked : walkPath spec.logicalRows (effectiveBits spec.physicalConfig).toNat q.va fuel spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root with
  | none => simp only [walked] at found; contradiction
  | some result =>
    cases result with
    | translationFault level => simp only [walked] at found; contradiction
    | addressSizeFault level => simp only [walked] at found; contradiction
    | leaf leafLevel logical physical view =>
      cases chosen : StaticData.permissionCandidate spec config rows q fuel physical view with
      | none => simp only [walked,chosen,Option.isSome_none] at found; contradiction
      | some row =>
        unfold StaticData.permissionCandidate at chosen
        have member := List.mem_of_find?_eq_some chosen
        have selected := List.find?_some chosen
        simp only [Bool.and_eq_true,decide_eq_true_eq] at selected
        let data := accessDataOfWalk spec config rows q fuel leafLevel logical physical view walked
          row member selected.1 selected.2 lower accessEL nonsecure
        refine ⟨data,current_s1_access_of_check spec config rows mapping q data entry ?_⟩
        simpa only [checkCurrentS1Access,data,accessDataOfWalk,walked] using checked

def checkQueries {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (cap : Nat) (queries : List AccessQuery) (fuel : Nat) (entry : ArmCertWalk.State) : Bool :=
  decide (queries.length ≤ cap) && queries.all (fun q =>
    StaticData.checkData spec config rows q fuel && checkCurrentFromWalk spec config mapping q fuel entry)

theorem bounded {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {cap : Nat} {queries : List AccessQuery} {fuel : Nat} {entry : ArmCertWalk.State}
    (checked : checkQueries spec config rows mapping cap queries fuel entry = true) : queries.length ≤ cap := by
  simp only [checkQueries,Bool.and_eq_true] at checked
  exact of_decide_eq_true checked.1

theorem member_current {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {cap : Nat} {queries : List AccessQuery} {fuel : Nat} {entry : ArmCertWalk.State}
    (checked : checkQueries spec config rows mapping cap queries fuel entry = true)
    (q : AccessQuery) (member : q ∈ queries) :
    ∃ data : S1AccessData spec config rows q, CurrentS1AccessAt spec config rows mapping q data entry := by
  simp only [checkQueries,Bool.and_eq_true] at checked
  have each := List.all_eq_true.mp checked.2 q member
  simp only [Bool.and_eq_true] at each
  exact current_of_checks spec config rows mapping q fuel entry each.1 each.2

/-- Only raw queries, logical rows and one checked entry are inputs. The access
certificates needed by ClosedMembership are produced inside the proof. -/
theorem closed_selected (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sites : List SelectedMap.Site) (code : List (BitVec 64)) (cap fuel : Nat) (entry : ArmCertWalk.State)
    (domains : ∀ q ∈ SelectedRepresentatives.queries (QueryDescriptors.data false) (QueryDescriptors.data true)
      QueryDescriptors.fetch sites code, domain q.va)
    (checked : checkQueries spec config rows mapping cap
      (SelectedRepresentatives.queries (QueryDescriptors.data false) (QueryDescriptors.data true)
        QueryDescriptors.fetch sites code) fuel entry = true) :
    ClosedMembershipAt spec config rows mapping (SelectedMap.consumerMap sites code mapping table) entry := by
  intro va acc aligned size permitted
  obtain ⟨q,member,hva,hsize,agree⟩ := SelectedRepresentatives.query_cover
    (QueryDescriptors.data false) (QueryDescriptors.data true) QueryDescriptors.fetch
    (QueryDescriptors.data_shape false) (QueryDescriptors.data_shape true) QueryDescriptors.fetch_shape
    sites code va acc aligned size permitted
  have domainVA : domain va := by rw [← hva]; exact domains q member
  obtain ⟨data,current⟩ := member_current checked q member
  rcases q with ⟨v,⟨raw,a⟩,sz⟩
  change v = va at hva
  change sz = size at hsize
  subst v
  subst sz
  exact ⟨⟨va,⟨acc,aligned⟩,size⟩,rfl,rfl,rfl,rfl,domainVA,
    S1AccessData.transfer (r' := ⟨acc,aligned⟩) data agree,
    CurrentS1AccessAt.transfer (r' := ⟨acc,aligned⟩) current agree⟩

#print axioms checkCurrentFromWalk
#print axioms current_of_checks
#print axioms checkQueries
#print axioms bounded
#print axioms member_current
#print axioms closed_selected
end TranslateSpan.CheckedEntry
