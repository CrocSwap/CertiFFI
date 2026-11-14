import TranslateMem.PageLeaf
import ArmCertTranslateModel.NativeWalkBinding

/-! RegionsInjective from the run's walk facts at ACCESSED VAs, with no LeafTranslated tie.
* `AccessLeaf`: at the start VA of every plan data access the mapping is a stage-1 leaf output address — what E17
  gives at each translated access (`WalkResultAdmitted`: mapping q.va = outputAddress q.va level base contig).
* `DataBytesLinear` (Memory's existing premise of memV_k) carries a 16-byte access's start PA to its interior bytes.
  It is the one off-walk fact: 30 tracked frame bytes (sp−31..−17, sp−15..−1, the interiors of the two 16-byte frame
  pairs) are never a translated VA; the other 98 tracked bytes are access starts.
* `NoDoubleMapPA`: two tracked bytes whose PAs share a 4 KiB frame lie in the same VA page (no double mmap).
Every tracked byte lies in some access (`covered`, decided) and keeps its in-page offset (`byte_offset`), so distinct
tracked bytes (distinct VAs by `RegionsDisjoint`) have distinct PAs. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateMem
open ArmCertValue ArmCertValue.HeapV2Mem ArmCert.Translate.Model

/-- E17 at every access start: the mapping there is a leaf output address. -/
def AccessLeaf (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Prop :=
  ∀ e ∈ HeapV2Plan.symbolicAccesses, ∃ l : Leaf,
    mapping (HeapV2E17.dataVA p e) = some (leafPA (HeapV2E17.dataVA p e) l)

/-- E17's walk fact at a translated query is an `AccessLeaf` instance: the mapping is the leaf output address. -/
theorem leaf_of_walk {params : ArmFull.S1TTWParams} {mapping : BitVec 64 → Option Nat} {regs : ArmFull.Regs}
    {query : AccessQuery} {level : Nat} {result : ArmFull.FaultRecord × ArmFull.AddressDescriptor × ArmFull.TTWState × BitVec 64}
    (h : WalkResultAdmitted params mapping regs query level result) :
    ∃ l : Leaf, mapping query.va = some (leafPA query.va l) :=
  ⟨(level, result.2.2.1.baseaddress, result.2.2.1.contiguous == 1#1), h.2.2.2.2.2.1⟩

/-- DEPLOYMENT (no double mmap), on the tracked bytes' PAs. -/
def NoDoubleMapPA (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Prop :=
  ∀ a, a ∈ heapv2Bytes → ∀ b, b ∈ heapv2Bytes → ∀ n m,
    mapping (byteVA p a.1 a.2) = some n → mapping (byteVA p b.1 b.2) = some m → n / 4096 = m / 4096 →
      pageOf (byteVA p a.1 a.2) = pageOf (byteVA p b.1 b.2)

/-- A leaf output address keeps the in-page offset. -/
theorem leafPA_mod (va : BitVec 64) (l : Leaf) : leafPA va l % 4096 = va.toNat % 4096 := by
  rw [leafPA_eq, mod_split va.toNat _ (leafSize_ge l)]
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ leafSize l = 4096 * K :=
    ⟨2 ^ (leafSize l - 12), by rw [show (4096 : Nat) = 2 ^ 12 from rfl, ← Nat.pow_add]; congr 1; have := leafSize_ge l; omega⟩
  rw [hK]
  have hB : l.2.1.address.toNat / (4096 * K) * (4096 * K) = 4096 * (l.2.1.address.toNat / (4096 * K) * K) := by
    ac_rfl
  rw [hB]
  have := Nat.mod_lt va.toNat (by decide : 0 < 4096)
  omega

def coveredBy (a : Region × Nat) (e : Nat × Nat × Int × Nat × Bool) : Bool :=
  e.2.1 == a.1.pin && decide (e.2.2.1 ≤ a.1.off + a.2) && decide (a.1.off + a.2 < e.2.2.1 + e.2.2.2.1)

set_option maxRecDepth 100000 in
/-- Every tracked byte lies inside some plan access. -/
theorem covered : heapv2Bytes.all (fun a => HeapV2Plan.symbolicAccesses.any (coveredBy a)) = true := by decide +kernel

theorem region_pin (a : Region × Nat) (h : a ∈ heapv2Bytes) : a.1.pin = 0 ∨ a.1.pin = 1 ∨ a.1.pin = 2 := by
  rcases mem_heapv2Bytes h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide

/-- Every tracked byte maps, keeping its in-page offset. -/
theorem byte_offset (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (hd : RegionsDisjoint p)
    (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0) (walk : AccessLeaf p mapping)
    (dbl : DataBytesLinear p mapping) :
    ∀ a, a ∈ heapv2Bytes → ∃ n, mapping (byteVA p a.1 a.2) = some n ∧ n % 4096 = (byteVA p a.1 a.2).toNat % 4096 := by
  obtain ⟨b0, b1, b2, b3, -, -, -⟩ := hd
  obtain ⟨aS, a0, a1⟩ := aligned
  intro a ha
  obtain ⟨e, he, hc⟩ := List.any_eq_true.1 (List.all_eq_true.1 covered a ha)
  have ok := List.all_eq_true.1 accesses_ok e he
  obtain ⟨k, pn, off, size, w⟩ := e
  simp only [coveredBy, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hpin, lo⟩, hi⟩ := hc
  simp only [accessOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  obtain ⟨hr, blk⟩ := ok
  -- the byte is the access's byte i
  let i : Nat := (a.1.off + a.2 - off).toNat
  have hi' : i < size := by simp only [i]; omega
  have hpos : (a.1.off + a.2 - off) = (i : Int) := by simp only [i]; omega
  -- DataBytesLinear at (access, i)
  have d := List.all_eq_true.1 dbl _ he
  have d := List.all_eq_true.1 d i (List.mem_range.2 hi')
  rw [beq_iff_eq] at d
  obtain ⟨l, hl⟩ := walk _ he
  simp only [HeapV2E17.dataVA] at hl d
  -- the base pin value
  have hbase : ∀ base : Nat, base % 16 = 0 → 0 ≤ (base : Int) + off → (base : Int) + off + size ≤ 2 ^ 64 →
      HeapV2E17.pin p pn = base →
      ∃ n, mapping (byteVA p a.1 a.2) = some n ∧ n % 4096 = (byteVA p a.1 a.2).toNat % 4096 := by
    intro base hal h0 h1 hp
    have hv : byteVA p a.1 a.2 = BitVec.ofInt 64 ((HeapV2E17.pin p pn : Int) + off + (i : Int)) := by
      unfold byteVA; congr 1; rw [hp, ← hpin]; simp only [pinv, hp]; omega
    have t1 : (BitVec.ofInt 64 ((base : Int) + off + (i : Int))).toNat = ((base : Int) + off).toNat + i := by
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by simp; omega)]; omega
    have t0 : (BitVec.ofInt 64 ((base : Int) + off)).toNat = ((base : Int) + off).toNat := by
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by simp; omega)]
    rw [hp] at d hl hv
    refine ⟨leafPA (BitVec.ofInt 64 ((base : Int) + off)) l + i, ?_, ?_⟩
    · rw [hv, d, hl]; rfl
    · rw [hv, t1, Nat.add_mod, leafPA_mod, t0]
      have m := Nat.mod_lt (((base : Int) + off).toNat) (by decide : 0 < 4096)
      have : ((base : Int) + off).toNat % 4096 + i < 4096 := by omega
      rw [Nat.mod_eq_of_lt (by omega : i < 4096), Nat.mod_eq_of_lt this, Nat.add_mod,
        Nat.mod_eq_of_lt (by omega : i < 4096), Nat.mod_eq_of_lt this]
  rcases hr with ⟨⟨rfl, lo'⟩, hi''⟩ | ⟨⟨rfl | rfl, lo'⟩, hi''⟩
  · exact hbase p.sp aS (by omega) (by omega) rfl
  · exact hbase p.x0 a0 (by omega) (by omega) rfl
  · exact hbase p.x1 a1 (by omega) (by omega) rfl

/-- **RegionsInjective** from E17 at the access starts, Memory's DataBytesLinear, the caller's regions and no double
    mmap: no LeafTranslated tie. -/
theorem regionsInjective_of_walk (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (hd : RegionsDisjoint p)
    (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0) (walk : AccessLeaf p mapping)
    (dbl : DataBytesLinear p mapping) (nd : NoDoubleMapPA p mapping) : RegionsInjective p mapping := by
  intro a ha b hb hne n hn hm
  obtain ⟨n1, h1, o1⟩ := byte_offset p mapping hd aligned walk dbl a ha
  obtain ⟨n2, h2, o2⟩ := byte_offset p mapping hd aligned walk dbl b hb
  rw [h1] at hn; rw [h2] at hm
  cases hn; cases hm
  have hp := nd a ha b hb n n h1 h2 rfl
  apply byteVA_injective p hd a ha b hb hne
  apply BitVec.eq_of_toNat_eq
  unfold pageOf at hp
  have := Nat.div_add_mod (byteVA p a.1 a.2).toNat 4096
  have := Nat.div_add_mod (byteVA p b.1 b.2).toNat 4096
  omega

#print axioms leaf_of_walk
#print axioms covered
#print axioms byte_offset
#print axioms regionsInjective_of_walk
end TranslateMem
