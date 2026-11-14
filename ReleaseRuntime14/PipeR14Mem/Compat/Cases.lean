-- C1 adapters: all concrete source/layout certificates are discharged, not extra deployment premises.
import PipeR14Mem.Compat.Core
import TranslateSpan.R14TrimmedSites
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model ArmCertValue
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace PipeR14.Compat

def hybridView_c00 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c00 p) mapping
theorem sources_c00 (p : R14E17.Pins) : AnchorSources p dataSites_c00 regions_c00 (PipeR14.TrimmedAnchors.sites_c00 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c00,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨((.pin 31 (-32)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c00 ∈ regions_c00;decide),(by change 0+16 ≤ 8*G31_c00.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c00).pin : Int) + (G31_c00).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-32)) + (t : Int) := by
      simp [G31_c00,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-32))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-16)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c00 ∈ regions_c00;decide),(by change 16+16 ≤ 8*G31_c00.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c00).pin : Int) + (G31_c00).off + (16 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-16)) + (t : Int) := by
      simp [G31_c00,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-16))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G1_c00 ∈ regions_c00;decide),(by change 0+4 ≤ 8*G1_c00.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c00).pin : Int) + (G1_c00).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (0)) + (t : Int) := by
      simp [G1_c00,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (8)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G1_c00 ∈ regions_c00;decide),(by change 8+8 ≤ 8*G1_c00.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c00).pin : Int) + (G1_c00).off + (8 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (8)) + (t : Int) := by
      simp [G1_c00,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (8))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c00 ∈ regions_c00;decide),(by change 0+4 ≤ 8*G0_c00.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c00).pin : Int) + (G0_c00).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c00,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.indirect "x0+mem64[x1+8]+24"),1),by decide,rfl,rfl,(by change 1=1 ∨ 1=4 ∨ 1=8 ∨ 1=16;decide),(by change G32_c00 ∈ regions_c00;decide),(by change 0+1 ≤ 8*G32_c00.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G32_c00).pin : Int) + (G32_c00).off + (0 + t : Nat)) =
        R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24") + (t : Int) := by
      simp [G32_c00,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24")) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c00 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c00 regions_c00 sc base) :
    DataStartsR14 mapping p footprint dataSites_c00 regions_c00 (PipeR14.TrimmedAnchors.sites_c00 p) sc base :=
  starts_of_legacy ds (sources_c00 p)

theorem legacyInputView_c00 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c00 regions_c00 sc base) (r : Region) (j : Nat) :
    hybridView_c00 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c00 p) r j

theorem gapView_c00 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c00 p) (r,j) = none) :
    hybridView_c00 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c00 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c00 regions_c00 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c00 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c00, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c00 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c00 p) s hs pa mp
def routeSpans_c00 : List (Region × Nat × Nat) := [(G31_c00,0,16), (G31_c00,16,16), (G1_c00,0,4), (G1_c00,8,8), (G1_c00,0,4), (G0_c00,0,4), (G32_c00,0,1), (G0_c00,0,4), (G31_c00,16,16), (G31_c00,0,16)]
theorem routesCovered_c00 (p : R14E17.Pins) :
    routeSpans_c00.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c00 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c00 (p : R14E17.Pins) :
    outMemLocs_c00.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c00 p) a).isSome) = true := rfl
#print axioms C1_c00
#print axioms legacyInputView_c00
#print axioms gapView_c00
#print axioms storeMiss_c00
#print axioms routesCovered_c00
#print axioms outputsCovered_c00

def hybridView_c01 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c01 p) mapping
theorem sources_c01 (p : R14E17.Pins) : AnchorSources p dataSites_c01 regions_c01 (PipeR14.TrimmedAnchors.sites_c01 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c01,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨((.pin 31 (-32)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c01 ∈ regions_c01;decide),(by change 0+16 ≤ 8*G31_c01.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c01).pin : Int) + (G31_c01).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-32)) + (t : Int) := by
      simp [G31_c01,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-32))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-16)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c01 ∈ regions_c01;decide),(by change 16+16 ≤ 8*G31_c01.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c01).pin : Int) + (G31_c01).off + (16 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-16)) + (t : Int) := by
      simp [G31_c01,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-16))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G1_c01 ∈ regions_c01;decide),(by change 0+4 ≤ 8*G1_c01.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c01).pin : Int) + (G1_c01).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (0)) + (t : Int) := by
      simp [G1_c01,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (8)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G1_c01 ∈ regions_c01;decide),(by change 8+8 ≤ 8*G1_c01.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c01).pin : Int) + (G1_c01).off + (8 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (8)) + (t : Int) := by
      simp [G1_c01,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (8))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c01 ∈ regions_c01;decide),(by change 0+4 ≤ 8*G0_c01.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c01).pin : Int) + (G0_c01).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c01,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.indirect "x0+mem64[x1+8]+24"),1),by decide,rfl,rfl,(by change 1=1 ∨ 1=4 ∨ 1=8 ∨ 1=16;decide),(by change G32_c01 ∈ regions_c01;decide),(by change 0+1 ≤ 8*G32_c01.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G32_c01).pin : Int) + (G32_c01).off + (0 + t : Nat)) =
        R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24") + (t : Int) := by
      simp [G32_c01,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24")) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c01 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c01 regions_c01 sc base) :
    DataStartsR14 mapping p footprint dataSites_c01 regions_c01 (PipeR14.TrimmedAnchors.sites_c01 p) sc base :=
  starts_of_legacy ds (sources_c01 p)

theorem legacyInputView_c01 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c01 regions_c01 sc base) (r : Region) (j : Nat) :
    hybridView_c01 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c01 p) r j

theorem gapView_c01 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c01 p) (r,j) = none) :
    hybridView_c01 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c01 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c01 regions_c01 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c01 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c01, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c01 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c01 p) s hs pa mp
def routeSpans_c01 : List (Region × Nat × Nat) := [(G31_c01,0,16), (G31_c01,16,16), (G1_c01,0,4), (G1_c01,8,8), (G0_c01,0,4), (G32_c01,0,1), (G0_c01,0,4), (G31_c01,16,16), (G31_c01,0,16)]
theorem routesCovered_c01 (p : R14E17.Pins) :
    routeSpans_c01.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c01 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c01 (p : R14E17.Pins) :
    outMemLocs_c01.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c01 p) a).isSome) = true := rfl
#print axioms C1_c01
#print axioms legacyInputView_c01
#print axioms gapView_c01
#print axioms storeMiss_c01
#print axioms routesCovered_c01
#print axioms outputsCovered_c01

def hybridView_c02 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c02 p) mapping
theorem sources_c02 (p : R14E17.Pins) : AnchorSources p dataSites_c02 regions_c02 (PipeR14.TrimmedAnchors.sites_c02 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c02,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨((.pin 31 (-32)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c02 ∈ regions_c02;decide),(by change 0+16 ≤ 8*G31_c02.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c02).pin : Int) + (G31_c02).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-32)) + (t : Int) := by
      simp [G31_c02,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-32))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-16)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c02 ∈ regions_c02;decide),(by change 16+16 ≤ 8*G31_c02.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c02).pin : Int) + (G31_c02).off + (16 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-16)) + (t : Int) := by
      simp [G31_c02,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-16))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G1_c02 ∈ regions_c02;decide),(by change 0+4 ≤ 8*G1_c02.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c02).pin : Int) + (G1_c02).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (0)) + (t : Int) := by
      simp [G1_c02,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (8)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G1_c02 ∈ regions_c02;decide),(by change 8+8 ≤ 8*G1_c02.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c02).pin : Int) + (G1_c02).off + (8 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (8)) + (t : Int) := by
      simp [G1_c02,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (8))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c02 ∈ regions_c02;decide),(by change 0+4 ≤ 8*G0_c02.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c02).pin : Int) + (G0_c02).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c02,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.indirect "x0+mem64[x1+8]+24"),1),by decide,rfl,rfl,(by change 1=1 ∨ 1=4 ∨ 1=8 ∨ 1=16;decide),(by change G32_c02 ∈ regions_c02;decide),(by change 0+1 ≤ 8*G32_c02.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G32_c02).pin : Int) + (G32_c02).off + (0 + t : Nat)) =
        R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24") + (t : Int) := by
      simp [G32_c02,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24")) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c02 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c02 regions_c02 sc base) :
    DataStartsR14 mapping p footprint dataSites_c02 regions_c02 (PipeR14.TrimmedAnchors.sites_c02 p) sc base :=
  starts_of_legacy ds (sources_c02 p)

theorem legacyInputView_c02 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c02 regions_c02 sc base) (r : Region) (j : Nat) :
    hybridView_c02 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c02 p) r j

theorem gapView_c02 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c02 p) (r,j) = none) :
    hybridView_c02 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c02 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c02 regions_c02 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c02 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c02, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c02 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c02 p) s hs pa mp
def routeSpans_c02 : List (Region × Nat × Nat) := [(G31_c02,0,16), (G31_c02,16,16), (G1_c02,0,4), (G1_c02,8,8), (G1_c02,0,4), (G0_c02,0,4), (G32_c02,0,1), (G31_c02,16,16), (G31_c02,0,16)]
theorem routesCovered_c02 (p : R14E17.Pins) :
    routeSpans_c02.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c02 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c02 (p : R14E17.Pins) :
    outMemLocs_c02.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c02 p) a).isSome) = true := rfl
#print axioms C1_c02
#print axioms legacyInputView_c02
#print axioms gapView_c02
#print axioms storeMiss_c02
#print axioms routesCovered_c02
#print axioms outputsCovered_c02

def hybridView_c03 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c03 p) mapping
theorem sources_c03 (p : R14E17.Pins) : AnchorSources p dataSites_c03 regions_c03 (PipeR14.TrimmedAnchors.sites_c03 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c03,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨((.pin 31 (-32)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c03 ∈ regions_c03;decide),(by change 0+16 ≤ 8*G31_c03.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c03).pin : Int) + (G31_c03).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-32)) + (t : Int) := by
      simp [G31_c03,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-32))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-16)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c03 ∈ regions_c03;decide),(by change 16+16 ≤ 8*G31_c03.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c03).pin : Int) + (G31_c03).off + (16 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-16)) + (t : Int) := by
      simp [G31_c03,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-16))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G1_c03 ∈ regions_c03;decide),(by change 0+4 ≤ 8*G1_c03.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c03).pin : Int) + (G1_c03).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (0)) + (t : Int) := by
      simp [G1_c03,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (8)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G1_c03 ∈ regions_c03;decide),(by change 8+8 ≤ 8*G1_c03.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c03).pin : Int) + (G1_c03).off + (8 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (8)) + (t : Int) := by
      simp [G1_c03,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (8))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c03 ∈ regions_c03;decide),(by change 0+4 ≤ 8*G0_c03.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c03).pin : Int) + (G0_c03).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c03,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.indirect "x0+mem64[x1+8]+24"),1),by decide,rfl,rfl,(by change 1=1 ∨ 1=4 ∨ 1=8 ∨ 1=16;decide),(by change G32_c03 ∈ regions_c03;decide),(by change 0+1 ≤ 8*G32_c03.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G32_c03).pin : Int) + (G32_c03).off + (0 + t : Nat)) =
        R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24") + (t : Int) := by
      simp [G32_c03,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24")) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c03 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c03 regions_c03 sc base) :
    DataStartsR14 mapping p footprint dataSites_c03 regions_c03 (PipeR14.TrimmedAnchors.sites_c03 p) sc base :=
  starts_of_legacy ds (sources_c03 p)

theorem legacyInputView_c03 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c03 regions_c03 sc base) (r : Region) (j : Nat) :
    hybridView_c03 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c03 p) r j

theorem gapView_c03 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c03 p) (r,j) = none) :
    hybridView_c03 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c03 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c03 regions_c03 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c03 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c03, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c03 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c03 p) s hs pa mp
def routeSpans_c03 : List (Region × Nat × Nat) := [(G31_c03,0,16), (G31_c03,16,16), (G1_c03,0,4), (G1_c03,8,8), (G0_c03,0,4), (G32_c03,0,1), (G31_c03,16,16), (G31_c03,0,16)]
theorem routesCovered_c03 (p : R14E17.Pins) :
    routeSpans_c03.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c03 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c03 (p : R14E17.Pins) :
    outMemLocs_c03.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c03 p) a).isSome) = true := rfl
#print axioms C1_c03
#print axioms legacyInputView_c03
#print axioms gapView_c03
#print axioms storeMiss_c03
#print axioms routesCovered_c03
#print axioms outputsCovered_c03

def hybridView_c04 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c04 p) mapping
theorem sources_c04 (p : R14E17.Pins) : AnchorSources p dataSites_c04 regions_c04 (PipeR14.TrimmedAnchors.sites_c04 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c04,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · refine ⟨((.pin 31 (-32)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c04 ∈ regions_c04;decide),(by change 0+16 ≤ 8*G31_c04.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c04).pin : Int) + (G31_c04).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-32)) + (t : Int) := by
      simp [G31_c04,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-32))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-16)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G31_c04 ∈ regions_c04;decide),(by change 16+8 ≤ 8*G31_c04.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c04).pin : Int) + (G31_c04).off + (16 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-16)) + (t : Int) := by
      simp [G31_c04,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-16))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (8)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G0_c04 ∈ regions_c04;decide),(by change 8+8 ≤ 8*G0_c04.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c04).pin : Int) + (G0_c04).off + (8 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (8)) + (t : Int) := by
      simp [G0_c04,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (8))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.indirect "x0+UBFM64[1,63](x1)+24"),1),by decide,rfl,rfl,(by change 1=1 ∨ 1=4 ∨ 1=8 ∨ 1=16;decide),(by change G33_c04 ∈ regions_c04;decide),(by change 0+1 ≤ 8*G33_c04.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G33_c04).pin : Int) + (G33_c04).off + (0 + t : Nat)) =
        R14E17.baseVA p (.indirect "x0+UBFM64[1,63](x1)+24") + (t : Int) := by
      simp [G33_c04,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.indirect "x0+UBFM64[1,63](x1)+24")) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c04 ∈ regions_c04;decide),(by change 0+4 ≤ 8*G0_c04.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c04).pin : Int) + (G0_c04).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c04,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c04 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c04 regions_c04 sc base) :
    DataStartsR14 mapping p footprint dataSites_c04 regions_c04 (PipeR14.TrimmedAnchors.sites_c04 p) sc base :=
  starts_of_legacy ds (sources_c04 p)

theorem legacyInputView_c04 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c04 regions_c04 sc base) (r : Region) (j : Nat) :
    hybridView_c04 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c04 p) r j

theorem gapView_c04 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c04 p) (r,j) = none) :
    hybridView_c04 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c04 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c04 regions_c04 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c04 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c04, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c04 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c04 p) s hs pa mp
def routeSpans_c04 : List (Region × Nat × Nat) := [(G31_c04,0,16), (G31_c04,16,8), (G0_c04,8,8), (G33_c04,0,1), (G0_c04,0,4), (G0_c04,0,4), (G31_c04,16,8), (G31_c04,0,16)]
theorem routesCovered_c04 (p : R14E17.Pins) :
    routeSpans_c04.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c04 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c04 (p : R14E17.Pins) :
    outMemLocs_c04.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c04 p) a).isSome) = true := rfl
#print axioms C1_c04
#print axioms legacyInputView_c04
#print axioms gapView_c04
#print axioms storeMiss_c04
#print axioms routesCovered_c04
#print axioms outputsCovered_c04

def hybridView_c05 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c05 p) mapping
theorem sources_c05 (p : R14E17.Pins) : AnchorSources p dataSites_c05 regions_c05 (PipeR14.TrimmedAnchors.sites_c05 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c05,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · refine ⟨((.pin 31 (-32)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c05 ∈ regions_c05;decide),(by change 0+16 ≤ 8*G31_c05.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c05).pin : Int) + (G31_c05).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-32)) + (t : Int) := by
      simp [G31_c05,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-32))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-16)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G31_c05 ∈ regions_c05;decide),(by change 16+8 ≤ 8*G31_c05.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c05).pin : Int) + (G31_c05).off + (16 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-16)) + (t : Int) := by
      simp [G31_c05,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-16))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (8)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G0_c05 ∈ regions_c05;decide),(by change 8+8 ≤ 8*G0_c05.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c05).pin : Int) + (G0_c05).off + (8 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (8)) + (t : Int) := by
      simp [G0_c05,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (8))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.indirect "x0+UBFM64[1,63](x1)+24"),1),by decide,rfl,rfl,(by change 1=1 ∨ 1=4 ∨ 1=8 ∨ 1=16;decide),(by change G33_c05 ∈ regions_c05;decide),(by change 0+1 ≤ 8*G33_c05.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G33_c05).pin : Int) + (G33_c05).off + (0 + t : Nat)) =
        R14E17.baseVA p (.indirect "x0+UBFM64[1,63](x1)+24") + (t : Int) := by
      simp [G33_c05,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.indirect "x0+UBFM64[1,63](x1)+24")) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c05 ∈ regions_c05;decide),(by change 0+4 ≤ 8*G0_c05.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c05).pin : Int) + (G0_c05).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c05,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c05 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c05 regions_c05 sc base) :
    DataStartsR14 mapping p footprint dataSites_c05 regions_c05 (PipeR14.TrimmedAnchors.sites_c05 p) sc base :=
  starts_of_legacy ds (sources_c05 p)

theorem legacyInputView_c05 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c05 regions_c05 sc base) (r : Region) (j : Nat) :
    hybridView_c05 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c05 p) r j

theorem gapView_c05 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c05 p) (r,j) = none) :
    hybridView_c05 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c05 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c05 regions_c05 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c05 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c05, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c05 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c05 p) s hs pa mp
def routeSpans_c05 : List (Region × Nat × Nat) := [(G31_c05,0,16), (G31_c05,16,8), (G0_c05,8,8), (G33_c05,0,1), (G0_c05,0,4), (G31_c05,16,8), (G31_c05,0,16)]
theorem routesCovered_c05 (p : R14E17.Pins) :
    routeSpans_c05.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c05 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c05 (p : R14E17.Pins) :
    outMemLocs_c05.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c05 p) a).isSome) = true := rfl
#print axioms C1_c05
#print axioms legacyInputView_c05
#print axioms gapView_c05
#print axioms storeMiss_c05
#print axioms routesCovered_c05
#print axioms outputsCovered_c05

def hybridView_c06 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c06 p) mapping
theorem sources_c06 (p : R14E17.Pins) : AnchorSources p dataSites_c06 regions_c06 (PipeR14.TrimmedAnchors.sites_c06 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c06,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨((.pin 31 (-48)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c06 ∈ regions_c06;decide),(by change 0+16 ≤ 8*G31_c06.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c06).pin : Int) + (G31_c06).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-48)) + (t : Int) := by
      simp [G31_c06,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-48))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-32)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G31_c06 ∈ regions_c06;decide),(by change 16+8 ≤ 8*G31_c06.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c06).pin : Int) + (G31_c06).off + (16 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-32)) + (t : Int) := by
      simp [G31_c06,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-32))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-16)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c06 ∈ regions_c06;decide),(by change 32+16 ≤ 8*G31_c06.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c06).pin : Int) + (G31_c06).off + (32 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-16)) + (t : Int) := by
      simp [G31_c06,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-16))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G1_c06 ∈ regions_c06;decide),(by change 0+4 ≤ 8*G1_c06.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c06).pin : Int) + (G1_c06).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (0)) + (t : Int) := by
      simp [G1_c06,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (8)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G1_c06 ∈ regions_c06;decide),(by change 8+8 ≤ 8*G1_c06.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c06).pin : Int) + (G1_c06).off + (8 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (8)) + (t : Int) := by
      simp [G1_c06,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (8))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c06 ∈ regions_c06;decide),(by change 0+4 ≤ 8*G0_c06.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c06).pin : Int) + (G0_c06).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c06,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.indirect "x0+mem64[x1+8]+24"),1),by decide,rfl,rfl,(by change 1=1 ∨ 1=4 ∨ 1=8 ∨ 1=16;decide),(by change G32_c06 ∈ regions_c06;decide),(by change 0+1 ≤ 8*G32_c06.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G32_c06).pin : Int) + (G32_c06).off + (0 + t : Nat)) =
        R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24") + (t : Int) := by
      simp [G32_c06,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24")) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c06 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c06 regions_c06 sc base) :
    DataStartsR14 mapping p footprint dataSites_c06 regions_c06 (PipeR14.TrimmedAnchors.sites_c06 p) sc base :=
  starts_of_legacy ds (sources_c06 p)

theorem legacyInputView_c06 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c06 regions_c06 sc base) (r : Region) (j : Nat) :
    hybridView_c06 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c06 p) r j

theorem gapView_c06 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c06 p) (r,j) = none) :
    hybridView_c06 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c06 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c06 regions_c06 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c06 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c06, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c06 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c06 p) s hs pa mp
def routeSpans_c06 : List (Region × Nat × Nat) := [(G31_c06,0,16), (G31_c06,16,8), (G31_c06,32,16), (G1_c06,0,4), (G1_c06,8,8), (G1_c06,0,4), (G0_c06,0,4), (G32_c06,0,1), (G31_c06,32,16), (G31_c06,16,8), (G31_c06,0,16)]
theorem routesCovered_c06 (p : R14E17.Pins) :
    routeSpans_c06.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c06 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c06 (p : R14E17.Pins) :
    outMemLocs_c06.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c06 p) a).isSome) = true := rfl
#print axioms C1_c06
#print axioms legacyInputView_c06
#print axioms gapView_c06
#print axioms storeMiss_c06
#print axioms routesCovered_c06
#print axioms outputsCovered_c06

def hybridView_c07 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c07 p) mapping
theorem sources_c07 (p : R14E17.Pins) : AnchorSources p dataSites_c07 regions_c07 (PipeR14.TrimmedAnchors.sites_c07 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c07,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨((.pin 31 (-48)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c07 ∈ regions_c07;decide),(by change 0+16 ≤ 8*G31_c07.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c07).pin : Int) + (G31_c07).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-48)) + (t : Int) := by
      simp [G31_c07,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-48))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-32)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G31_c07 ∈ regions_c07;decide),(by change 16+8 ≤ 8*G31_c07.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c07).pin : Int) + (G31_c07).off + (16 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-32)) + (t : Int) := by
      simp [G31_c07,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-32))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 31 (-16)),16),by decide,rfl,rfl,(by change 16=1 ∨ 16=4 ∨ 16=8 ∨ 16=16;decide),(by change G31_c07 ∈ regions_c07;decide),(by change 32+16 ≤ 8*G31_c07.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G31_c07).pin : Int) + (G31_c07).off + (32 + t : Nat)) =
        R14E17.baseVA p (.pin 31 (-16)) + (t : Int) := by
      simp [G31_c07,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 31 (-16))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G1_c07 ∈ regions_c07;decide),(by change 0+4 ≤ 8*G1_c07.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c07).pin : Int) + (G1_c07).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (0)) + (t : Int) := by
      simp [G1_c07,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 1 (8)),8),by decide,rfl,rfl,(by change 8=1 ∨ 8=4 ∨ 8=8 ∨ 8=16;decide),(by change G1_c07 ∈ regions_c07;decide),(by change 8+8 ≤ 8*G1_c07.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G1_c07).pin : Int) + (G1_c07).off + (8 + t : Nat)) =
        R14E17.baseVA p (.pin 1 (8)) + (t : Int) := by
      simp [G1_c07,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 1 (8))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c07 ∈ regions_c07;decide),(by change 0+4 ≤ 8*G0_c07.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c07).pin : Int) + (G0_c07).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c07,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
  · refine ⟨((.indirect "x0+mem64[x1+8]+24"),1),by decide,rfl,rfl,(by change 1=1 ∨ 1=4 ∨ 1=8 ∨ 1=16;decide),(by change G32_c07 ∈ regions_c07;decide),(by change 0+1 ≤ 8*G32_c07.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G32_c07).pin : Int) + (G32_c07).off + (0 + t : Nat)) =
        R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24") + (t : Int) := by
      simp [G32_c07,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.indirect "x0+mem64[x1+8]+24")) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c07 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c07 regions_c07 sc base) :
    DataStartsR14 mapping p footprint dataSites_c07 regions_c07 (PipeR14.TrimmedAnchors.sites_c07 p) sc base :=
  starts_of_legacy ds (sources_c07 p)

theorem legacyInputView_c07 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c07 regions_c07 sc base) (r : Region) (j : Nat) :
    hybridView_c07 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c07 p) r j

theorem gapView_c07 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c07 p) (r,j) = none) :
    hybridView_c07 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c07 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c07 regions_c07 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c07 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c07, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c07 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c07 p) s hs pa mp
def routeSpans_c07 : List (Region × Nat × Nat) := [(G31_c07,0,16), (G31_c07,16,8), (G31_c07,32,16), (G1_c07,0,4), (G1_c07,8,8), (G0_c07,0,4), (G32_c07,0,1), (G31_c07,32,16), (G31_c07,16,8), (G31_c07,0,16)]
theorem routesCovered_c07 (p : R14E17.Pins) :
    routeSpans_c07.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c07 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c07 (p : R14E17.Pins) :
    outMemLocs_c07.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c07 p) a).isSome) = true := rfl
#print axioms C1_c07
#print axioms legacyInputView_c07
#print axioms gapView_c07
#print axioms storeMiss_c07
#print axioms routesCovered_c07
#print axioms outputsCovered_c07

def hybridView_c08 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c08 p) mapping
theorem sources_c08 (p : R14E17.Pins) : AnchorSources p dataSites_c08 regions_c08 (PipeR14.TrimmedAnchors.sites_c08 p) := by
  constructor
  intro s hs
  simp [PipeR14.TrimmedAnchors.sites_c08] at hs
theorem C1_c08 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c08 regions_c08 sc base) :
    DataStartsR14 mapping p footprint dataSites_c08 regions_c08 (PipeR14.TrimmedAnchors.sites_c08 p) sc base :=
  starts_of_legacy ds (sources_c08 p)

theorem legacyInputView_c08 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c08 regions_c08 sc base) (r : Region) (j : Nat) :
    hybridView_c08 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c08 p) r j

theorem gapView_c08 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c08 p) (r,j) = none) :
    hybridView_c08 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c08 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c08 regions_c08 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c08 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c08, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c08 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c08 p) s hs pa mp
def routeSpans_c08 : List (Region × Nat × Nat) := []
theorem routesCovered_c08 (p : R14E17.Pins) :
    routeSpans_c08.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c08 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c08 (p : R14E17.Pins) :
    outMemLocs_c08.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c08 p) a).isSome) = true := rfl
#print axioms C1_c08
#print axioms legacyInputView_c08
#print axioms gapView_c08
#print axioms storeMiss_c08
#print axioms routesCovered_c08
#print axioms outputsCovered_c08

def hybridView_c09 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c09 p) mapping
theorem sources_c09 (p : R14E17.Pins) : AnchorSources p dataSites_c09 regions_c09 (PipeR14.TrimmedAnchors.sites_c09 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c09,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c09 ∈ regions_c09;decide),(by change 0+4 ≤ 8*G0_c09.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c09).pin : Int) + (G0_c09).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c09,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c09 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c09 regions_c09 sc base) :
    DataStartsR14 mapping p footprint dataSites_c09 regions_c09 (PipeR14.TrimmedAnchors.sites_c09 p) sc base :=
  starts_of_legacy ds (sources_c09 p)

theorem legacyInputView_c09 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c09 regions_c09 sc base) (r : Region) (j : Nat) :
    hybridView_c09 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c09 p) r j

theorem gapView_c09 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c09 p) (r,j) = none) :
    hybridView_c09 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c09 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c09 regions_c09 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c09 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c09, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c09 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c09 p) s hs pa mp
def routeSpans_c09 : List (Region × Nat × Nat) := [(G0_c09,0,4), (G0_c09,0,4)]
theorem routesCovered_c09 (p : R14E17.Pins) :
    routeSpans_c09.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c09 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c09 (p : R14E17.Pins) :
    outMemLocs_c09.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c09 p) a).isSome) = true := rfl
#print axioms C1_c09
#print axioms legacyInputView_c09
#print axioms gapView_c09
#print axioms storeMiss_c09
#print axioms routesCovered_c09
#print axioms outputsCovered_c09

def hybridView_c10 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c10 p) mapping
theorem sources_c10 (p : R14E17.Pins) : AnchorSources p dataSites_c10 regions_c10 (PipeR14.TrimmedAnchors.sites_c10 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c10,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl
  · refine ⟨((.pin 0 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G0_c10 ∈ regions_c10;decide),(by change 0+4 ≤ 8*G0_c10.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G0_c10).pin : Int) + (G0_c10).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 0 (0)) + (t : Int) := by
      simp [G0_c10,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 0 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c10 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c10 regions_c10 sc base) :
    DataStartsR14 mapping p footprint dataSites_c10 regions_c10 (PipeR14.TrimmedAnchors.sites_c10 p) sc base :=
  starts_of_legacy ds (sources_c10 p)

theorem legacyInputView_c10 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c10 regions_c10 sc base) (r : Region) (j : Nat) :
    hybridView_c10 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c10 p) r j

theorem gapView_c10 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c10 p) (r,j) = none) :
    hybridView_c10 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c10 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c10 regions_c10 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c10 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c10, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c10 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c10 p) s hs pa mp
def routeSpans_c10 : List (Region × Nat × Nat) := [(G0_c10,0,4)]
theorem routesCovered_c10 (p : R14E17.Pins) :
    routeSpans_c10.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c10 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c10 (p : R14E17.Pins) :
    outMemLocs_c10.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c10 p) a).isSome) = true := rfl
#print axioms C1_c10
#print axioms legacyInputView_c10
#print axioms gapView_c10
#print axioms storeMiss_c10
#print axioms routesCovered_c10
#print axioms outputsCovered_c10

def hybridView_c11 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c11 p) mapping
theorem sources_c11 (p : R14E17.Pins) : AnchorSources p dataSites_c11 regions_c11 (PipeR14.TrimmedAnchors.sites_c11 p) := by
  constructor
  intro s hs
  simp [PipeR14.TrimmedAnchors.sites_c11] at hs
theorem C1_c11 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c11 regions_c11 sc base) :
    DataStartsR14 mapping p footprint dataSites_c11 regions_c11 (PipeR14.TrimmedAnchors.sites_c11 p) sc base :=
  starts_of_legacy ds (sources_c11 p)

theorem legacyInputView_c11 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c11 regions_c11 sc base) (r : Region) (j : Nat) :
    hybridView_c11 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c11 p) r j

theorem gapView_c11 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c11 p) (r,j) = none) :
    hybridView_c11 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c11 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c11 regions_c11 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c11 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c11, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c11 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c11 p) s hs pa mp
def routeSpans_c11 : List (Region × Nat × Nat) := []
theorem routesCovered_c11 (p : R14E17.Pins) :
    routeSpans_c11.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c11 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c11 (p : R14E17.Pins) :
    outMemLocs_c11.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c11 p) a).isSome) = true := rfl
#print axioms C1_c11
#print axioms legacyInputView_c11
#print axioms gapView_c11
#print axioms storeMiss_c11
#print axioms routesCovered_c11
#print axioms outputsCovered_c11

def hybridView_c12 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c12 p) mapping
theorem sources_c12 (p : R14E17.Pins) : AnchorSources p dataSites_c12 regions_c12 (PipeR14.TrimmedAnchors.sites_c12 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c12,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl
  · refine ⟨((.pin 19 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G19_c12 ∈ regions_c12;decide),(by change 0+4 ≤ 8*G19_c12.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G19_c12).pin : Int) + (G19_c12).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 19 (0)) + (t : Int) := by
      simp [G19_c12,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 19 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c12 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c12 regions_c12 sc base) :
    DataStartsR14 mapping p footprint dataSites_c12 regions_c12 (PipeR14.TrimmedAnchors.sites_c12 p) sc base :=
  starts_of_legacy ds (sources_c12 p)

theorem legacyInputView_c12 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c12 regions_c12 sc base) (r : Region) (j : Nat) :
    hybridView_c12 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c12 p) r j

theorem gapView_c12 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c12 p) (r,j) = none) :
    hybridView_c12 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c12 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c12 regions_c12 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c12 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c12, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c12 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c12 p) s hs pa mp
def routeSpans_c12 : List (Region × Nat × Nat) := [(G19_c12,0,4), (G19_c12,0,4)]
theorem routesCovered_c12 (p : R14E17.Pins) :
    routeSpans_c12.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c12 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c12 (p : R14E17.Pins) :
    outMemLocs_c12.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c12 p) a).isSome) = true := rfl
#print axioms C1_c12
#print axioms legacyInputView_c12
#print axioms gapView_c12
#print axioms storeMiss_c12
#print axioms routesCovered_c12
#print axioms outputsCovered_c12

def hybridView_c13 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) := hybridView p (PipeR14.TrimmedAnchors.sites_c13 p) mapping
theorem sources_c13 (p : R14E17.Pins) : AnchorSources p dataSites_c13 regions_c13 (PipeR14.TrimmedAnchors.sites_c13 p) := by
  constructor
  intro s hs
  simp only [PipeR14.TrimmedAnchors.sites_c13,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl
  · refine ⟨((.pin 19 (0)),4),by decide,rfl,rfl,(by change 4=1 ∨ 4=4 ∨ 4=8 ∨ 4=16;decide),(by change G19_c13 ∈ regions_c13;decide),(by change 0+4 ≤ 8*G19_c13.words;decide),?_⟩
    intro t ht
    have raw : ((PipeR14.pinv p (G19_c13).pin : Int) + (G19_c13).off + (0 + t : Nat)) =
        R14E17.baseVA p (.pin 19 (0)) + (t : Int) := by
      simp [G19_c13,PipeR14.pinv,R14E17.baseVA] <;> omega
    change BitVec.ofInt 64 _ = BitVec.ofInt 64 (R14E17.baseVA p (.pin 19 (0))) + BitVec.ofNat 64 t
    rw [raw,BitVec.ofInt_add,BitVec.ofInt_natCast]
theorem C1_c13 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c13 regions_c13 sc base) :
    DataStartsR14 mapping p footprint dataSites_c13 regions_c13 (PipeR14.TrimmedAnchors.sites_c13 p) sc base :=
  starts_of_legacy ds (sources_c13 p)

theorem legacyInputView_c13 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c13 regions_c13 sc base) (r : Region) (j : Nat) :
    hybridView_c13 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  hybrid_eq_legacy ds (sources_c13 p) r j

theorem gapView_c13 (p : R14E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c13 p) (r,j) = none) :
    hybridView_c13 p mapping r j = mapping (PipeR14.regionVA p r j) :=
  gap_identity p _ mapping r j gap

theorem storeMiss_c13 {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint dataSites_c13 regions_c13 sc base) (s : TranslateSpan.Site) (hs : s ∈ PipeR14.TrimmedAnchors.sites_c13 p)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions_c13, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
      ∀ q, hybridView_c13 p mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size) :=
  legacy_store_miss ds (sources_c13 p) s hs pa mp
def routeSpans_c13 : List (Region × Nat × Nat) := [(G19_c13,0,4)]
theorem routesCovered_c13 (p : R14E17.Pins) :
    routeSpans_c13.all (fun a => (List.range a.2.2).all (fun t =>
      (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c13 p) (a.1,a.2.1+t)).isSome)) = true := rfl

theorem outputsCovered_c13 (p : R14E17.Pins) :
    outMemLocs_c13.all (fun a => (TranslateSpan.selected (PipeR14.TrimmedAnchors.sites_c13 p) a).isSome) = true := rfl
#print axioms C1_c13
#print axioms legacyInputView_c13
#print axioms gapView_c13
#print axioms storeMiss_c13
#print axioms routesCovered_c13
#print axioms outputsCovered_c13
end PipeR14.Compat
