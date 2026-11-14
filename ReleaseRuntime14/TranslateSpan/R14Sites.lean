-- Revised access view: actual-sized anchors, legacy-VA fallback on never-accessed padding.
import PipeR14Mem.Compat.Cases
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model ArmCertValue
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PipeR14.AccessAnchors
abbrev regionVA := PipeR14.regionVA
abbrev dataAcc := PipeR14.TrimmedAnchors.dataAcc
abbrev dataAcc_shape := PipeR14.TrimmedAnchors.dataAcc_shape

abbrev sites_c00 := PipeR14.TrimmedAnchors.sites_c00
abbrev bytePA_c00 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c00 p mapping
abbrev current_c00 := @PipeR14.TrimmedAnchors.current_c00
abbrev geometry_c00 := PipeR14.TrimmedAnchors.geometry_c00
abbrev complete_c00 := PipeR14.TrimmedAnchors.complete_c00
abbrev bounded_c00 := PipeR14.TrimmedAnchors.bounded_c00

theorem positive_c00 : R14Plan.accesses_c00.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c00 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c00
      R14Plan.codeWords_c00 R14Plan.entry_c00 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c00, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c00, ∀ r' ∈ regions_c00, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c00)
    (r : Region) (hr : r ∈ regions_c00) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c00 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c00 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c00 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c00 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c00 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c00 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c00

abbrev sites_c01 := PipeR14.TrimmedAnchors.sites_c01
abbrev bytePA_c01 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c01 p mapping
abbrev current_c01 := @PipeR14.TrimmedAnchors.current_c01
abbrev geometry_c01 := PipeR14.TrimmedAnchors.geometry_c01
abbrev complete_c01 := PipeR14.TrimmedAnchors.complete_c01
abbrev bounded_c01 := PipeR14.TrimmedAnchors.bounded_c01

theorem positive_c01 : R14Plan.accesses_c01.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c01 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c01
      R14Plan.codeWords_c01 R14Plan.entry_c01 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c01, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c01, ∀ r' ∈ regions_c01, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c01)
    (r : Region) (hr : r ∈ regions_c01) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c01 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c01 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c01 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c01 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c01 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c01 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c01

abbrev sites_c02 := PipeR14.TrimmedAnchors.sites_c02
abbrev bytePA_c02 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c02 p mapping
abbrev current_c02 := @PipeR14.TrimmedAnchors.current_c02
abbrev geometry_c02 := PipeR14.TrimmedAnchors.geometry_c02
abbrev complete_c02 := PipeR14.TrimmedAnchors.complete_c02
abbrev bounded_c02 := PipeR14.TrimmedAnchors.bounded_c02

theorem positive_c02 : R14Plan.accesses_c02.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c02 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c02
      R14Plan.codeWords_c02 R14Plan.entry_c02 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c02, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c02, ∀ r' ∈ regions_c02, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c02)
    (r : Region) (hr : r ∈ regions_c02) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c02 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c02 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c02 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c02 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c02 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c02 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c02

abbrev sites_c03 := PipeR14.TrimmedAnchors.sites_c03
abbrev bytePA_c03 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c03 p mapping
abbrev current_c03 := @PipeR14.TrimmedAnchors.current_c03
abbrev geometry_c03 := PipeR14.TrimmedAnchors.geometry_c03
abbrev complete_c03 := PipeR14.TrimmedAnchors.complete_c03
abbrev bounded_c03 := PipeR14.TrimmedAnchors.bounded_c03

theorem positive_c03 : R14Plan.accesses_c03.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c03 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c03
      R14Plan.codeWords_c03 R14Plan.entry_c03 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c03, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c03, ∀ r' ∈ regions_c03, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c03)
    (r : Region) (hr : r ∈ regions_c03) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c03 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c03 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c03 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c03 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c03 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c03 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c03

abbrev sites_c04 := PipeR14.TrimmedAnchors.sites_c04
abbrev bytePA_c04 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c04 p mapping
abbrev current_c04 := @PipeR14.TrimmedAnchors.current_c04
abbrev geometry_c04 := PipeR14.TrimmedAnchors.geometry_c04
abbrev complete_c04 := PipeR14.TrimmedAnchors.complete_c04
abbrev bounded_c04 := PipeR14.TrimmedAnchors.bounded_c04

theorem positive_c04 : R14Plan.accesses_c04.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c04 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c04
      R14Plan.codeWords_c04 R14Plan.entry_c04 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c04, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c04, ∀ r' ∈ regions_c04, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c04)
    (r : Region) (hr : r ∈ regions_c04) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c04 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c04 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c04 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c04 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c04 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c04 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c04

abbrev sites_c05 := PipeR14.TrimmedAnchors.sites_c05
abbrev bytePA_c05 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c05 p mapping
abbrev current_c05 := @PipeR14.TrimmedAnchors.current_c05
abbrev geometry_c05 := PipeR14.TrimmedAnchors.geometry_c05
abbrev complete_c05 := PipeR14.TrimmedAnchors.complete_c05
abbrev bounded_c05 := PipeR14.TrimmedAnchors.bounded_c05

theorem positive_c05 : R14Plan.accesses_c05.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c05 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c05
      R14Plan.codeWords_c05 R14Plan.entry_c05 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c05, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c05, ∀ r' ∈ regions_c05, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c05)
    (r : Region) (hr : r ∈ regions_c05) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c05 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c05 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c05 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c05 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c05 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c05 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c05

abbrev sites_c06 := PipeR14.TrimmedAnchors.sites_c06
abbrev bytePA_c06 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c06 p mapping
abbrev current_c06 := @PipeR14.TrimmedAnchors.current_c06
abbrev geometry_c06 := PipeR14.TrimmedAnchors.geometry_c06
abbrev complete_c06 := PipeR14.TrimmedAnchors.complete_c06
abbrev bounded_c06 := PipeR14.TrimmedAnchors.bounded_c06

theorem positive_c06 : R14Plan.accesses_c06.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c06 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c06
      R14Plan.codeWords_c06 R14Plan.entry_c06 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c06, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c06, ∀ r' ∈ regions_c06, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c06)
    (r : Region) (hr : r ∈ regions_c06) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c06 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c06 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c06 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c06 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c06 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c06 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c06

abbrev sites_c07 := PipeR14.TrimmedAnchors.sites_c07
abbrev bytePA_c07 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c07 p mapping
abbrev current_c07 := @PipeR14.TrimmedAnchors.current_c07
abbrev geometry_c07 := PipeR14.TrimmedAnchors.geometry_c07
abbrev complete_c07 := PipeR14.TrimmedAnchors.complete_c07
abbrev bounded_c07 := PipeR14.TrimmedAnchors.bounded_c07

theorem positive_c07 : R14Plan.accesses_c07.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c07 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c07
      R14Plan.codeWords_c07 R14Plan.entry_c07 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c07, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c07, ∀ r' ∈ regions_c07, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c07)
    (r : Region) (hr : r ∈ regions_c07) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c07 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c07 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c07 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c07 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c07 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c07 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c07

abbrev sites_c08 := PipeR14.TrimmedAnchors.sites_c08
abbrev bytePA_c08 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c08 p mapping
abbrev current_c08 := @PipeR14.TrimmedAnchors.current_c08
abbrev geometry_c08 := PipeR14.TrimmedAnchors.geometry_c08
abbrev complete_c08 := PipeR14.TrimmedAnchors.complete_c08
abbrev bounded_c08 := PipeR14.TrimmedAnchors.bounded_c08

theorem positive_c08 : R14Plan.accesses_c08.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c08 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c08
      R14Plan.codeWords_c08 R14Plan.entry_c08 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c08, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c08, ∀ r' ∈ regions_c08, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c08)
    (r : Region) (hr : r ∈ regions_c08) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c08 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c08 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c08 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c08 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c08 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c08 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c08

abbrev sites_c09 := PipeR14.TrimmedAnchors.sites_c09
abbrev bytePA_c09 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c09 p mapping
abbrev current_c09 := @PipeR14.TrimmedAnchors.current_c09
abbrev geometry_c09 := PipeR14.TrimmedAnchors.geometry_c09
abbrev complete_c09 := PipeR14.TrimmedAnchors.complete_c09
abbrev bounded_c09 := PipeR14.TrimmedAnchors.bounded_c09

theorem positive_c09 : R14Plan.accesses_c09.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c09 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c09
      R14Plan.codeWords_c09 R14Plan.entry_c09 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c09, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c09, ∀ r' ∈ regions_c09, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c09)
    (r : Region) (hr : r ∈ regions_c09) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c09 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c09 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c09 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c09 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c09 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c09 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c09

abbrev sites_c10 := PipeR14.TrimmedAnchors.sites_c10
abbrev bytePA_c10 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c10 p mapping
abbrev current_c10 := @PipeR14.TrimmedAnchors.current_c10
abbrev geometry_c10 := PipeR14.TrimmedAnchors.geometry_c10
abbrev complete_c10 := PipeR14.TrimmedAnchors.complete_c10
abbrev bounded_c10 := PipeR14.TrimmedAnchors.bounded_c10

theorem positive_c10 : R14Plan.accesses_c10.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c10 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c10
      R14Plan.codeWords_c10 R14Plan.entry_c10 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c10, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c10, ∀ r' ∈ regions_c10, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c10)
    (r : Region) (hr : r ∈ regions_c10) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c10 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c10 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c10 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c10 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c10 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c10 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c10

abbrev sites_c11 := PipeR14.TrimmedAnchors.sites_c11
abbrev bytePA_c11 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c11 p mapping
abbrev current_c11 := @PipeR14.TrimmedAnchors.current_c11
abbrev geometry_c11 := PipeR14.TrimmedAnchors.geometry_c11
abbrev complete_c11 := PipeR14.TrimmedAnchors.complete_c11
abbrev bounded_c11 := PipeR14.TrimmedAnchors.bounded_c11

theorem positive_c11 : R14Plan.accesses_c11.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c11 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c11
      R14Plan.codeWords_c11 R14Plan.entry_c11 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c11, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c11, ∀ r' ∈ regions_c11, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c11)
    (r : Region) (hr : r ∈ regions_c11) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c11 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c11 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c11 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c11 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c11 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c11 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c11

abbrev sites_c12 := PipeR14.TrimmedAnchors.sites_c12
abbrev bytePA_c12 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c12 p mapping
abbrev current_c12 := @PipeR14.TrimmedAnchors.current_c12
abbrev geometry_c12 := PipeR14.TrimmedAnchors.geometry_c12
abbrev complete_c12 := PipeR14.TrimmedAnchors.complete_c12
abbrev bounded_c12 := PipeR14.TrimmedAnchors.bounded_c12

theorem positive_c12 : R14Plan.accesses_c12.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c12 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c12
      R14Plan.codeWords_c12 R14Plan.entry_c12 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c12, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c12, ∀ r' ∈ regions_c12, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c12)
    (r : Region) (hr : r ∈ regions_c12) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c12 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c12 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c12 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c12 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c12 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c12 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c12

abbrev sites_c13 := PipeR14.TrimmedAnchors.sites_c13
abbrev bytePA_c13 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := PipeR14.Compat.hybridView_c13 p mapping
abbrev current_c13 := @PipeR14.TrimmedAnchors.current_c13
abbrev geometry_c13 := PipeR14.TrimmedAnchors.geometry_c13
abbrev complete_c13 := PipeR14.TrimmedAnchors.complete_c13
abbrev bounded_c13 := PipeR14.TrimmedAnchors.bounded_c13

theorem positive_c13 : R14Plan.accesses_c13.all (fun a => decide (0 < a.2.2.1)) = true := by decide

theorem span_c13 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : R14E17.Pins} {loadBase : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c13
      R14Plan.codeWords_c13 R14Plan.entry_c13 p loadBase mapping table) state)
    (image : TopologyImageAt spec state)
    (aligned : ∀ a ∈ R14Plan.accesses_c13, (R14E17.dataVA p a.2.1).toNat % a.2.2.1 = 0)
    (sp16 : p.regs 31 % 16 = 0)
    (distinct : ∀ r ∈ regions_c13, ∀ r' ∈ regions_c13, ∀ j j',
      j < 8*r.words → j' < 8*r'.words → regionVA p r j = regionVA p r' j' → r=r' ∧ j=j')
    (a : R14E17.Access) (ha : a ∈ R14Plan.accesses_c13)
    (r : Region) (hr : r ∈ regions_c13) (j0 : Nat) (hw : j0+a.2.2.1 ≤ 8*r.words)
    (layout : ∀ t, t < a.2.2.1 → regionVA p r (j0+t) = R14E17.dataVA p a.2.1 + BitVec.ofNat 64 t) :
    ∀ t, t < a.2.2.1 → bytePA_c13 p mapping r (j0+t) = (mapping (R14E17.dataVA p a.2.1)).map (·+t) := by
  have old := PipeR14.TrimmedAnchors.span_c13 closed image aligned sp16 distinct a ha r hr j0 hw layout
  obtain ⟨s,hs,good⟩ := List.any_eq_true.1 (List.all_eq_true.1 (complete_c13 p) a ha)
  obtain ⟨start,size⟩ := of_decide_eq_true good
  have cov := PipeR14.Compat.covered_of_layout (PipeR14.Compat.sources_c13 p) distinct s hs r hr j0 a.2.2.1 size
    (of_decide_eq_true (List.all_eq_true.1 positive_c13 a ha)) hw
    (fun t ht => by rw [start];exact layout t ht)
  intro t ht
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.1 (cov t ht)
  change PipeR14.Compat.hybridView p (sites_c13 p) mapping r (j0+t) = _
  rw [PipeR14.Compat.covered_identity p _ mapping r (j0+t) q hq]
  exact old t ht
#print axioms span_c13
end PipeR14.AccessAnchors
