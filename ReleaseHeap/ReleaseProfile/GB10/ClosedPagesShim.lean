import ReleaseProfile.GB10.ClosedPages
import Bridge.CruxGenGuarded.ConsumerMapShim

set_option autoImplicit false

/-! Closed membership over the shim consumer map, split from `ClosedPages` so worlds without
`Bridge.CruxGenGuarded.ConsumerMapShim` (Runtime) can use the core. -/

namespace ReleaseProfile.GB10.ClosedPages

open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate ArmCert.Translate.Model

/-! ## Generic closed-with-pages over the shim consumer map (ControlRowsFullNormalClosure.synthetic_closed_shim,
made generic in spec/config/rows/mapping/pins/base and the representative lists) -/

theorem closed_pages_shim {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) {queries : List AccessQuery}
    (readReps : List (Representative spec config rows queries (DataShape false)))
    (writeReps : List (Representative spec config rows queries (DataShape true)))
    (fetchReps : List (Representative spec config rows queries FetchShape))
    (lr : ∀ r ∈ readReps, r.level = 3) (lw : ∀ r ∈ writeReps, r.level = 3) (lf : ∀ r ∈ fetchReps, r.level = 3)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ queries, SamePage q0.va q.va) → domain q)
    (R : Regs) (p : HeapV2E17.Pins) (base : Nat) (table : Nat → Prop)
    (hd : HeapV2Plan.symbolicAccesses.all (fun a => if a.2.2.2.2
      then accessOK spec config rows mapping writeReps R (HeapV2E17.dataVA p a) (a.2.2.2.1 : Int)
      else accessOK spec config rows mapping readReps R (HeapV2E17.dataVA p a) (a.2.2.2.1 : Int)) = true)
    (hcode : HeapV2Plan.codeWords.all (fun c => accessOK spec config rows mapping fetchReps R (HeapV2E17.codeVA base c.1) 4) = true)
    (hshim : HeapV2ShimPlan.codeWords.all
      (fun c => accessOK spec config rows mapping fetchReps R (HeapV2E17.shimCodeVA base c.1) 4) = true)
    (hslotR : accessOK spec config rows mapping readReps R (BitVec.ofNat 64 p.sp) 16 = true)
    (hslotW : accessOK spec config rows mapping writeReps R (BitVec.ofNat 64 p.sp) 16 = true)
    (state : ArmCertWalk.State) (regs : state.regs = R) :
    ClosedPagesAt spec config rows mapping (HeapV2E17.consumerMapShim (fun _ => True) p base mapping table) state := by
  intro va acc aligned size permitted
  rcases permitted with (⟨a, member, _, hva, hsize, shape⟩ | ⟨c, member, hva, hsize, shape⟩) |
      ⟨c, member, hva, hsize, shape⟩ | ⟨w, hva, hsize, shape⟩
  · have h := List.all_eq_true.1 hd a member
    subst hva; subst hsize
    cases hw : a.2.2.2.2
    · rw [hw] at shape
      simp only [hw, Bool.false_eq_true, ite_false] at h
      obtain ⟨dom, r, data, rshape, lvl, current⟩ :=
        access_case_pages spec config rows mapping readReps lr R _ _ h state regs
      exact ⟨⟨_, ⟨acc, aligned⟩, _⟩, rfl, rfl, rfl, rfl, hdom _ dom,
        S1AccessData.transfer data (rshape.agree shape), lvl, CurrentS1AccessAt.transfer current (rshape.agree shape)⟩
    · rw [hw] at shape
      simp only [hw, ite_true] at h
      obtain ⟨dom, r, data, rshape, lvl, current⟩ :=
        access_case_pages spec config rows mapping writeReps lw R _ _ h state regs
      exact ⟨⟨_, ⟨acc, aligned⟩, _⟩, rfl, rfl, rfl, rfl, hdom _ dom,
        S1AccessData.transfer data (rshape.agree shape), lvl, CurrentS1AccessAt.transfer current (rshape.agree shape)⟩
  · subst hva; subst hsize
    obtain ⟨dom, r, data, rshape, lvl, current⟩ :=
      access_case_pages spec config rows mapping fetchReps lf R _ _ (List.all_eq_true.1 hcode c member) state regs
    exact ⟨⟨_, ⟨acc, aligned⟩, _⟩, rfl, rfl, rfl, rfl, hdom _ dom,
      S1AccessData.transfer data (rshape.agree shape), lvl, CurrentS1AccessAt.transfer current (rshape.agree shape)⟩
  · subst hva; subst hsize
    obtain ⟨dom, r, data, rshape, lvl, current⟩ :=
      access_case_pages spec config rows mapping fetchReps lf R _ _ (List.all_eq_true.1 hshim c member) state regs
    exact ⟨⟨_, ⟨acc, aligned⟩, _⟩, rfl, rfl, rfl, rfl, hdom _ dom,
      S1AccessData.transfer data (rshape.agree shape), lvl, CurrentS1AccessAt.transfer current (rshape.agree shape)⟩
  · subst hva; subst hsize
    cases w
    · obtain ⟨dom, r, data, rshape, lvl, current⟩ :=
        access_case_pages spec config rows mapping readReps lr R _ _ hslotR state regs
      exact ⟨⟨_, ⟨acc, aligned⟩, _⟩, rfl, rfl, rfl, rfl, hdom _ dom,
        S1AccessData.transfer data (rshape.agree shape), lvl, CurrentS1AccessAt.transfer current (rshape.agree shape)⟩
    · obtain ⟨dom, r, data, rshape, lvl, current⟩ :=
        access_case_pages spec config rows mapping writeReps lw R _ _ hslotW state regs
      exact ⟨⟨_, ⟨acc, aligned⟩, _⟩, rfl, rfl, rfl, rfl, hdom _ dom,
        S1AccessData.transfer data (rshape.agree shape), lvl, CurrentS1AccessAt.transfer current (rshape.agree shape)⟩

end ReleaseProfile.GB10.ClosedPages

#print axioms ReleaseProfile.GB10.ClosedPages.closed_pages_shim
