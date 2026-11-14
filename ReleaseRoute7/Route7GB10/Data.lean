-- Route 7 positive-C2 world (loops): the data facts at d = 0x31000, s = 0x30000, n = 1 shared by the three cases.
import Route7GB10.Common
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Route7GB10
open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10 ArmCertLoop ArmCertLoop.ContractDraft

def dA : BitVec 64 := 0x31000#64
def sA : BitVec 64 := 0x30000#64
def retA : BitVec 64 := 0x500000#64

theorem map_s : World.mapping (sA + BitVec.ofNat 64 0) = some 0x80600000 := by decide
theorem map_d : World.mapping (dA + BitVec.ofNat 64 0) = some 0x80601000 := by decide

theorem notTable (pa : Nat) (h : 0x80005000 ≤ pa) : ¬ (rowsFootprint World.imageRows).byte pa := by
  intro ⟨slot, hs, lo, hi⟩
  simp only [rowsFootprint, List.mem_map] at hs
  obtain ⟨row, rm, rfl⟩ := hs
  have hs := of_decide_eq_true (List.all_eq_true.1 Plan.slots_range row rm)
  have hw : (rowsFootprint World.imageRows).width = 8 := rfl
  omega

theorem codeWrite : CodeWriteSeparated World.mapping Plan.B dA 1 := by
  intro off h pa hpa ⟨i, hi, hd⟩
  rw [Plan.code_map off h] at hpa
  cases hpa
  have : i = 0 := by omega
  subst this
  rw [map_d] at hd
  have e := Option.some.inj hd
  unfold ContractDraft.codeScope at h
  simp only [Plan.codePA, Generated.imageStart, Generated.imageWords_length] at e h
  omega

theorem dataGeom_spans (ss : List SpanMap.Span)
    (hss : ∀ span ∈ ss, span.length = 1 ∧ (span.base = sA ∨ span.base = dA)) :
    ∀ span ∈ ss, ∀ i, i < span.length → ∃ pa : BitVec 56, World.mapping (SpanMap.byteVA span i) = some pa.toNat ∧
      MemM1.MemReadIF.NotMMIO pa ∧ ¬ (rowsFootprint World.imageRows).byte pa.toNat := by
  intro span hs i hi
  obtain ⟨len, hb⟩ := hss span hs
  have : i = 0 := by omega
  subst this
  rcases hb with hb | hb
  · refine ⟨0x80600000#56, ?_, ⟨by decide, by decide⟩, notTable _ (by decide)⟩
    simp only [SpanMap.byteVA, hb]; exact map_s
  · refine ⟨0x80601000#56, ?_, ⟨by decide, by decide⟩, notTable _ (by decide)⟩
    simp only [SpanMap.byteVA, hb]; exact map_d

theorem union_va (ss : List SpanMap.Span) (hss : ∀ span ∈ ss, span.length = 1 ∧ (span.base = sA ∨ span.base = dA))
    (a : BitVec 64) (h : SpanMap.InUnion ss a) : a = sA + BitVec.ofNat 64 0 ∨ a = dA + BitVec.ofNat 64 0 := by
  obtain ⟨span, hs, i, hi, ea⟩ := h
  obtain ⟨len, hb⟩ := hss span hs
  have : i = 0 := by omega
  subst this
  simp only [SpanMap.byteVA] at ea
  rcases hb with hb | hb <;> rw [hb] at ea
  · exact Or.inl ea
  · exact Or.inr ea

theorem injective_spans (ss : List SpanMap.Span) (hss : ∀ span ∈ ss, span.length = 1 ∧ (span.base = sA ∨ span.base = dA)) :
    SpanMap.UnionInjective World.mapping ss := by
  intro a b pa ia ib ma mb
  rcases union_va ss hss a ia with rfl | rfl <;> rcases union_va ss hss b ib with rfl | rfl
  · rfl
  · exact absurd (ma.trans mb.symm) (by decide)
  · exact absurd (ma.trans mb.symm) (by decide)
  · rfl

theorem src_byte (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (gprs : Vector (BitVec 64) 31) (entry : Nat) (pcount : BitVec 88) :
    readByte World.mapping (makeModelEntry sem rho caller (Plan.payload gprs entry pcount)) (sA + BitVec.ofNat 64 0) =
      some Plan.srcByte := by
  have hm := Plan.realizes sem rho caller gprs entry pcount (0x80600000, Plan.srcByte)
    (by simp [Plan.plan, Plan.dataPlan])
  simp only [readByte, map_s, Option.bind_some]
  exact hm

end Route7GB10
#print axioms Route7GB10.codeWrite
#print axioms Route7GB10.injective_spans
#print axioms Route7GB10.src_byte
