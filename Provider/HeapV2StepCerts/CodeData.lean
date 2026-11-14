-- Memory: memStep_k's codeD premise from a Boolean deployment check: every
-- code-word PA byte lies outside every plan data access's PA range (both 8-byte halves).
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.DataBytes
import ArmCertTranslateModel.C9TranslateBinding
import MemReloc.Placement
open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxRecDepth 100000
namespace HeapV2StepCerts.MemNext

/-- PA ranges [n, n + size) of every plan data access (both 8-byte halves' mappings). -/
def dataRanges (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : List (Nat × Nat) :=
  HeapV2Plan.symbolicAccesses.flatMap fun e =>
    [HeapV2E17.dataVA p e, plus8 (HeapV2E17.dataVA p e)].filterMap fun va =>
      (mapping va).map fun n => (n, n + e.2.2.2.1)

def outsideRanges (rs : List (Nat × Nat)) (pa : Nat) : Bool :=
  rs.all fun r => !(decide (r.1 ≤ pa) && decide (pa < r.2))

def checkOffsets (offs : List Nat) (rs : List (Nat × Nat)) (mapping : BitVec 64 → Option Nat) (base : BitVec 64) : Bool :=
  offs.all fun off =>
    match mapping (MemReloc.imageAddress base off) with
    | none => true
    | some pa => outsideRanges rs pa

def checkCodeDataDisjointWith (rs : List (Nat × Nat)) (mapping : BitVec 64 → Option Nat) (base : BitVec 64) : Bool :=
  codeOffsets.all fun off =>
    match mapping (MemReloc.imageAddress base off) with
    | none => true
    | some pa => outsideRanges rs pa

/-- Code-image bytes are disjoint from the plan's data bytes. -/
def checkCodeDataDisjoint (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (base : BitVec 64) : Bool :=
  checkCodeDataDisjointWith (dataRanges p mapping) mapping base

theorem codeD_of_check {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {base : BitVec 64}
    (chk : checkCodeDataDisjoint p mapping base = true) :
    ImageTableSeparated codeScope base mapping (dataBytes p mapping) := by
  intro offset pa hs hm ⟨e, he, va, n, hva, hmap, h1, h2⟩
  have c := List.all_eq_true.1 chk offset hs
  simp only [hm, outsideRanges, List.all_eq_true] at c
  have mem : (n, n + e.2.2.2.1) ∈ dataRanges p mapping := by
    refine List.mem_flatMap.2 ⟨e, he, List.mem_filterMap.2 ⟨va, ?_, by simp [hmap]⟩⟩
    rcases hva with rfl | rfl <;> simp
  have := c _ mem
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
  omega

#print axioms codeD_of_check
end HeapV2StepCerts.MemNext
