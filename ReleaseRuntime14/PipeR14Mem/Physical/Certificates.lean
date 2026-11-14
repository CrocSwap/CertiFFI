-- actual-access physical certificates; span/injectivity are derived from access certificates.
import PipeR14Mem.Physical.Static
import TranslateSpan.R14Sites
set_option autoImplicit false
namespace PipeR14.Physical
open ArmCertValue ArmCert.Translate.Model ArmCertWalk

abbrev DataStartsR14 := PipeR14.Compat.DataStartsR14

theorem site_mem {accs : List R14E17.Access} {a : R14E17.Access} (ha : a ∈ accs) :
    (a.2.1, a.2.2.1) ∈ sitesOf accs := by
  simp only [sitesOf, List.mem_eraseDups]
  exact List.mem_map.2 ⟨a, ha, rfl⟩

theorem access_of_site {accs : List R14E17.Access} {s : R14Plan.Base × Nat} (hs : s ∈ sitesOf accs) :
    ∃ a ∈ accs, (a.2.1, a.2.2.1) = s := by
  simp only [sitesOf, List.mem_eraseDups] at hs
  exact List.mem_map.1 hs

theorem dataStatic_c00 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c00 regions_c00 (AccessAnchors.sites_c00 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c00
      R14Plan.codeWords_c00 R14Plan.entry_c00 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c00 p mapping) p fp dataSites_c00 regions_c00 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c00, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c00 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c00

theorem dataStatic_c01 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c01 regions_c01 (AccessAnchors.sites_c01 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c01
      R14Plan.codeWords_c01 R14Plan.entry_c01 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c01 p mapping) p fp dataSites_c01 regions_c01 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c01, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c01 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c01

theorem dataStatic_c02 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c02 regions_c02 (AccessAnchors.sites_c02 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c02
      R14Plan.codeWords_c02 R14Plan.entry_c02 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c02 p mapping) p fp dataSites_c02 regions_c02 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c02, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c02 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c02

theorem dataStatic_c03 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c03 regions_c03 (AccessAnchors.sites_c03 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c03
      R14Plan.codeWords_c03 R14Plan.entry_c03 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c03 p mapping) p fp dataSites_c03 regions_c03 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c03, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c03 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c03

theorem dataStatic_c04 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c04 regions_c04 (AccessAnchors.sites_c04 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c04
      R14Plan.codeWords_c04 R14Plan.entry_c04 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c04 p mapping) p fp dataSites_c04 regions_c04 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c04, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c04 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c04

theorem dataStatic_c05 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c05 regions_c05 (AccessAnchors.sites_c05 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c05
      R14Plan.codeWords_c05 R14Plan.entry_c05 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c05 p mapping) p fp dataSites_c05 regions_c05 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c05, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c05 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c05

theorem dataStatic_c06 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c06 regions_c06 (AccessAnchors.sites_c06 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c06
      R14Plan.codeWords_c06 R14Plan.entry_c06 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c06 p mapping) p fp dataSites_c06 regions_c06 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c06, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c06 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c06

theorem dataStatic_c07 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c07 regions_c07 (AccessAnchors.sites_c07 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c07
      R14Plan.codeWords_c07 R14Plan.entry_c07 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c07 p mapping) p fp dataSites_c07 regions_c07 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c07, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c07 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c07

theorem dataStatic_c08 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c08 regions_c08 (AccessAnchors.sites_c08 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c08
      R14Plan.codeWords_c08 R14Plan.entry_c08 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c08 p mapping) p fp dataSites_c08 regions_c08 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c08, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c08 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c08

theorem dataStatic_c09 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c09 regions_c09 (AccessAnchors.sites_c09 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c09
      R14Plan.codeWords_c09 R14Plan.entry_c09 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c09 p mapping) p fp dataSites_c09 regions_c09 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c09, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c09 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c09

theorem dataStatic_c10 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c10 regions_c10 (AccessAnchors.sites_c10 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c10
      R14Plan.codeWords_c10 R14Plan.entry_c10 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c10 p mapping) p fp dataSites_c10 regions_c10 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c10, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c10 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c10

theorem dataStatic_c11 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c11 regions_c11 (AccessAnchors.sites_c11 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c11
      R14Plan.codeWords_c11 R14Plan.entry_c11 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c11 p mapping) p fp dataSites_c11 regions_c11 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c11, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c11 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c11

theorem dataStatic_c12 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c12 regions_c12 (AccessAnchors.sites_c12 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c12
      R14Plan.codeWords_c12 R14Plan.entry_c12 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c12 p mapping) p fp dataSites_c12 regions_c12 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c12, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c12 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c12

theorem dataStatic_c13 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    {fp : Nat → Prop} {sc : Nat → Prop} {base : BitVec 64}
    (st : DataStartsR14 mapping p fp dataSites_c13 regions_c13 (AccessAnchors.sites_c13 p) sc base)
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c13
      R14Plan.codeWords_c13 R14Plan.entry_c13 p loadBase mapping table) state)
    (image : TopologyImageAt spec state) :
    DataStaticR14 mapping (AccessAnchors.bytePA_c13 p mapping) p fp dataSites_c13 regions_c13 sc base := by
  have aligned : ∀ a ∈ R14Plan.accesses_c13, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0 := by
    intro a ha
    obtain ⟨pa, mp, mm, out, al⟩ := st.site (a.2.1,a.2.2.1) (site_mem ha)
    exact al
  refine ⟨st.site, st.sp16, st.code, ?_, ?_⟩
  · intro s hs r hr j0 hw layout t ht
    obtain ⟨a, ha, he⟩ := access_of_site hs
    obtain rfl := he
    exact AccessAnchors.span_c13 closed image aligned st.sp16 st.distinct a ha r hr j0 hw layout t ht
  · exact st.missAll

#print axioms dataStatic_c13

end PipeR14.Physical
