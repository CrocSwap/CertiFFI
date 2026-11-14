import ArmCertValueMem.Premises

/-! a design decision: the two value-layer memory premises of heap-v2 derived from page-level
deployment facts.
* `PageLinear mapping pages`: the VA→PA mapping is the 4 KiB page map (frame of the VA page, plus the in-page offset)
  — what the leaf descriptors of the translation give;
* `NoDoubleMapOn`: on the pages holding the tracked bytes, distinct VA pages have distinct frames (double mmap
  excluded: a deployment premise);
* `RegionsDisjoint`: the caller premise, the Int intervals [x1, x1+32), [x0, x0+32), [sp−64, sp) pairwise disjoint
  and inside [0, 2^64).
Then `RegionsInjective` (`regionsInjective_of_pages`), and, with sp 16-aligned, `DataBytesLinear`
(`dataBytesLinear_of_pages`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateMem
open ArmCertValue ArmCertValue.HeapV2Mem ArmCert.Translate.Model

def pageOf (va : BitVec 64) : Nat := va.toNat / 4096

/-- DEPLOYMENT: the mapping is page-linear over a 4 KiB page map. -/
def PageLinear (mapping : BitVec 64 → Option Nat) (pages : Nat → Option Nat) : Prop :=
  ∀ va, mapping va = (pages (pageOf va)).map fun f => f * 4096 + va.toNat % 4096

/-- DEPLOYMENT (no double mmap): on the pages of the tracked bytes, one frame per VA page. -/
def NoDoubleMapOn (p : HeapV2E17.Pins) (pages : Nat → Option Nat) : Prop :=
  ∀ a, a ∈ heapv2Bytes → ∀ b, b ∈ heapv2Bytes → ∀ f,
    pages (pageOf (byteVA p a.1 a.2)) = some f → pages (pageOf (byteVA p b.1 b.2)) = some f →
      pageOf (byteVA p a.1 a.2) = pageOf (byteVA p b.1 b.2)

/-- CALLER: the three regions are disjoint, non-wrapping VA intervals. -/
def RegionsDisjoint (p : HeapV2E17.Pins) : Prop :=
  p.x0 + 32 ≤ 2 ^ 64 ∧ p.x1 + 32 ≤ 2 ^ 64 ∧ 64 ≤ p.sp ∧ p.sp ≤ 2 ^ 64 ∧
    (p.x0 + 32 ≤ p.x1 ∨ p.x1 + 32 ≤ p.x0) ∧ (p.x0 + 32 + 64 ≤ p.sp ∨ p.sp ≤ p.x0) ∧
    (p.x1 + 32 + 64 ≤ p.sp ∨ p.sp ≤ p.x1)

/-- Page-linear + one frame per page: distinct VAs never share a PA. -/
theorem pa_distinct {mapping : BitVec 64 → Option Nat} {pages : Nat → Option Nat} (lin : PageLinear mapping pages)
    {va vb : BitVec 64} (hne : va ≠ vb) (samePage : ∀ f, pages (pageOf va) = some f → pages (pageOf vb) = some f →
      pageOf va = pageOf vb) (n : Nat) (ha : mapping va = some n) : mapping vb ≠ some n := by
  intro hb
  rw [lin] at ha hb
  obtain ⟨fa, hfa, rfl⟩ := Option.map_eq_some_iff.1 ha
  obtain ⟨fb, hfb, e⟩ := Option.map_eq_some_iff.1 hb
  have ra := Nat.mod_lt va.toNat (by decide : 0 < 4096)
  have rb := Nat.mod_lt vb.toNat (by decide : 0 < 4096)
  have hf : fb = fa := by omega
  subst hf
  have hp := samePage fb hfa hfb
  apply hne
  apply BitVec.eq_of_toNat_eq
  have ho : va.toNat % 4096 = vb.toNat % 4096 := by omega
  unfold pageOf at hp
  have := Nat.div_add_mod va.toNat 4096; have := Nat.div_add_mod vb.toNat 4096
  omega

theorem mem_heapv2Bytes {a : Region × Nat} (h : a ∈ heapv2Bytes) :
    (a.1 = HeapV2Plan.I ∧ a.2 < 32) ∨ (a.1 = HeapV2Plan.O ∧ a.2 < 32) ∨ (a.1 = HeapV2Plan.F ∧ a.2 < 64) := by
  simp only [heapv2Bytes, regions, HeapV2Plan.regions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact Or.inl ⟨rfl, by simpa [HeapV2Plan.I] using hj⟩
  · exact Or.inr (Or.inl ⟨rfl, by simpa [HeapV2Plan.O] using hj⟩)
  · exact Or.inr (Or.inr ⟨rfl, by simpa [HeapV2Plan.F] using hj⟩)

/-- The Int address of a tracked byte. -/
theorem byteVA_toNat (p : HeapV2E17.Pins) (r : Region) (j : Nat) (z : Int) (hz : z = (pinv p r.pin : Int) + r.off + j)
    (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) : (byteVA p r j).toNat = z.toNat := by
  unfold byteVA; rw [← hz, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt h0 (by simpa using h1)]

theorem byteVA_injective (p : HeapV2E17.Pins) (hd : RegionsDisjoint p) :
    ∀ a, a ∈ heapv2Bytes → ∀ b, b ∈ heapv2Bytes → a ≠ b → byteVA p a.1 a.2 ≠ byteVA p b.1 b.2 := by
  obtain ⟨h0, h1, h2, h3, d01, d0s, d1s⟩ := hd
  intro a ha b hb hne heq
  obtain ⟨ra, ja⟩ := a; obtain ⟨rb, jb⟩ := b
  have e := congrArg BitVec.toNat heq
  rcases mem_heapv2Bytes ha with ⟨rfl, hja⟩ | ⟨rfl, hja⟩ | ⟨rfl, hja⟩ <;>
  rcases mem_heapv2Bytes hb with ⟨rfl, hjb⟩ | ⟨rfl, hjb⟩ | ⟨rfl, hjb⟩ <;>
  simp only at hja hjb e hne <;>
  first
  | (rw [byteVA_toNat p _ ja _ rfl (by simp [HeapV2Plan.I, HeapV2Plan.O, HeapV2Plan.F, pinv, HeapV2E17.pin]; omega)
          (by simp [HeapV2Plan.I, HeapV2Plan.O, HeapV2Plan.F, pinv, HeapV2E17.pin]; omega),
        byteVA_toNat p _ jb _ rfl (by simp [HeapV2Plan.I, HeapV2Plan.O, HeapV2Plan.F, pinv, HeapV2E17.pin]; omega)
          (by simp [HeapV2Plan.I, HeapV2Plan.O, HeapV2Plan.F, pinv, HeapV2E17.pin]; omega)] at e
     simp [HeapV2Plan.I, HeapV2Plan.O, HeapV2Plan.F, pinv, HeapV2E17.pin] at e hne
     omega)

/-- **RegionsInjective** from the caller's disjoint regions and the page-level deployment facts. -/
theorem regionsInjective_of_pages (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (pages : Nat → Option Nat)
    (hd : RegionsDisjoint p) (lin : PageLinear mapping pages) (nd : NoDoubleMapOn p pages) :
    RegionsInjective p mapping := by
  intro a ha b hb hne n hn
  exact pa_distinct lin (byteVA_injective p hd a ha b hb hne) (fun f h1 h2 => nd a ha b hb f h1 h2) n hn

/-- Every plan data access stays in its region (sp: [−64, 0); x0/x1: [0, 32)) and inside one 16-byte block. -/
def accessOK (e : Nat × Nat × Int × Nat × Bool) : Bool :=
  ((e.2.1 == 0 && decide (-64 ≤ e.2.2.1) && decide (e.2.2.1 + e.2.2.2.1 ≤ 0)) ||
    ((e.2.1 == 1 || e.2.1 == 2) && decide (0 ≤ e.2.2.1) && decide (e.2.2.1 + e.2.2.2.1 ≤ 32))) &&
  decide (e.2.2.1 % 16 + e.2.2.2.1 ≤ 16)

set_option maxRecDepth 100000 in
theorem accesses_ok : HeapV2Plan.symbolicAccesses.all accessOK = true := by decide +kernel

/-- One access: its bytes map linearly (same page, offsets add). -/
theorem access_linear (mapping : BitVec 64 → Option Nat) (pages : Nat → Option Nat) (lin : PageLinear mapping pages)
    (base : Nat) (off : Int) (size : Nat) (hal : base % 16 = 0) (h0 : 0 ≤ (base : Int) + off)
    (h1 : (base : Int) + off + size ≤ 2 ^ 64) (blk : off % 16 + size ≤ 16) (i : Nat) (hi : i < size) :
    mapping (BitVec.ofInt 64 ((base : Int) + off + (i : Int))) = (mapping (BitVec.ofInt 64 ((base : Int) + off))).map (· + i) := by
  have t1 : (BitVec.ofInt 64 ((base : Int) + off + (i : Int))).toNat = ((base : Int) + off).toNat + i := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by simp; omega)]; omega
  have t0 : (BitVec.ofInt 64 ((base : Int) + off)).toNat = ((base : Int) + off).toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  rw [lin, lin, pageOf, pageOf, t1, t0]
  have same : (((base : Int) + off).toNat + i) / 4096 = ((base : Int) + off).toNat / 4096 := by omega
  rw [same]
  cases pages (((base : Int) + off).toNat / 4096) with
  | none => rfl
  | some f =>
    simp only [Option.map_some]
    exact congrArg some (by omega)

/-- **DataBytesLinear** from page linearity, the caller's region bounds and 16-byte alignment of sp, x0, x1. -/
theorem dataBytesLinear_of_pages (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (pages : Nat → Option Nat)
    (lin : PageLinear mapping pages) (hd : RegionsDisjoint p)
    (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0) : DataBytesLinear p mapping := by
  obtain ⟨b0, b1, b2, b3, -, -, -⟩ := hd
  obtain ⟨aS, a0, a1⟩ := aligned
  unfold DataBytesLinear
  rw [List.all_eq_true]
  intro e he
  have ok := List.all_eq_true.1 accesses_ok e he
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [beq_iff_eq]
  obtain ⟨k, pn, off, size, w⟩ := e
  simp only [accessOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  simp only [HeapV2E17.dataVA] at hi ⊢
  obtain ⟨hr, blk⟩ := ok
  rcases hr with ⟨⟨rfl, lo⟩, hi'⟩ | ⟨⟨rfl | rfl, lo⟩, hi'⟩
  · exact access_linear mapping pages lin p.sp off size aS (by omega)
      (by omega) blk i hi
  · exact access_linear mapping pages lin p.x0 off size a0 (by omega)
      (by omega) blk i hi
  · exact access_linear mapping pages lin p.x1 off size a1 (by omega)
      (by omega) blk i hi

#print axioms regionsInjective_of_pages
#print axioms dataBytesLinear_of_pages
end TranslateMem
