import Pilot.S2WriteBytes
import Pilot.S1Descriptor
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
namespace S1ByteMemory
abbrev Memory := Std.ExtHashMap Nat (BitVec 8)
abbrev State := SequentialState Regs oracleChoiceSource
def store (m : Memory) (a : Nat) (d : BitVec 64) : Memory :=
  let m := m.insert (a + 0) (d.extractLsb' 0 8)
  let m := m.insert (a + 1) (d.extractLsb' 8 8)
  let m := m.insert (a + 2) (d.extractLsb' 16 8)
  let m := m.insert (a + 3) (d.extractLsb' 24 8)
  let m := m.insert (a + 4) (d.extractLsb' 32 8)
  let m := m.insert (a + 5) (d.extractLsb' 40 8)
  let m := m.insert (a + 6) (d.extractLsb' 48 8)
  m.insert (a + 7) (d.extractLsb' 56 8)

theorem native_eq (a : Nat) (d : BitVec 64) (s : State) :
    S2WriteBytes.native a d s = .ok true {s with mem := store s.mem a d} := by rfl

theorem write_eq (a : Nat) (d : BitVec 64) (s : State) :
    (PreSail.writeBytes (n := 8) a d : SailM Bool) s =
      .ok true {s with mem := store s.mem a d} := by
  rw [S2WriteBytes.complete, native_eq]

theorem lookup_inside (m : Memory) (a : Nat) (d : BitVec 64) (i : Nat) (hi : i < 8) :
    (store m a d)[a + i]? = some (d.extractLsb' (8 * i) 8) := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [store, Std.ExtHashMap.getElem?_insert] <;> simp

theorem lookup_outside (m : Memory) (a : Nat) (d : BitVec 64) (x : Nat)
    (hx : x < a ∨ a + 8 ≤ x) : (store m a d)[x]? = m[x]? := by
  have hn : ∀ i < 8, a + i ≠ x := by intro i hi; omega
  have hzero : a ≠ x := by omega
  simp [store, Std.ExtHashMap.getElem?_insert,
    hzero, hn 1 (by decide), hn 2 (by decide), hn 3 (by decide),
    hn 4 (by decide), hn 5 (by decide), hn 6 (by decide), hn 7 (by decide)]

def DescAt (m : Memory) (a : Nat) (d : BitVec 64) : Prop :=
  ∀ i < 8, m[a + i]? = some (d.extractLsb' (8 * i) 8)

theorem stored_descriptor (m : Memory) (a : Nat) (d : BitVec 64) :
    DescAt (store m a d) a d := lookup_inside m a d

theorem other_descriptor (m : Memory) (a b : Nat) (d old : BitVec 64)
    (ha : a % 8 = 0) (hb : b % 8 = 0) (hne : a ≠ b) (hold : DescAt m b old) :
    DescAt (store m a d) b old := by
  intro i hi
  rw [lookup_outside m a d (b + i) (by omega)]
  exact hold i hi

theorem other_descriptor_iff (m : Memory) (a b : Nat) (d old : BitVec 64)
    (ha : a % 8 = 0) (hb : b % 8 = 0) (hne : a ≠ b) :
    DescAt (store m a d) b old ↔ DescAt m b old := by
  constructor
  · intro h i hi
    rw [← lookup_outside m a d (b + i) (by omega)]
    exact h i hi
  · exact other_descriptor m a b d old ha hb hne

theorem descriptor_unique (m : Memory) (a : Nat) (d e : BitVec 64)
    (hd : DescAt m a d) (he : DescAt m a e) : d = e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb : i / 8 < 8 := by omega
  have hbytes := Option.some.inj ((hd (i / 8) hb).symm.trans (he (i / 8) hb))
  have hbit := congrArg (fun x : BitVec 8 => x.getLsbD (i % 8)) hbytes
  have hr : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hindex : 8 * (i / 8) + i % 8 = i := by omega
  simpa only [BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and, hindex] using hbit

/-- Non-PIE descriptor view only. This is a local memory invariant, not yet a full map or source walk theorem. A word observation records actual bytes and the C36-stable descriptor view. -/
def Observed (ha hd : Bool) (m : Memory) (a : Nat) (v : S1Descriptor.View 64) : Prop :=
  ∃ d, DescAt m a d ∧ S1Descriptor.view ha hd d = v

/-- Equality of every aligned descriptor observation, including absence of bytes.
    It is independent of a particular table layout or translation proof. -/
def Equivalent (ha hd : Bool) (m m' : Memory) : Prop :=
  ∀ a, a % 8 = 0 → ∀ v, Observed ha hd m a v ↔ Observed ha hd m' a v

theorem store_equivalent (ha hd : Bool) (m : Memory) (a : Nat) (old new : BitVec 64)
    (halign : a % 8 = 0) (hold : DescAt m a old)
    (hview : S1Descriptor.view ha hd old = S1Descriptor.view ha hd new) :
    Equivalent ha hd m (store m a new) := by
  intro b hb v
  by_cases hab : a = b
  · subst b
    constructor
    · rintro ⟨d, hd, hv⟩
      have heq := descriptor_unique m a d old hd hold
      subst d
      exact ⟨new, stored_descriptor _ _ _, hview.symm.trans hv⟩
    · rintro ⟨d, hd, hv⟩
      have heq := descriptor_unique (store m a new) a d new hd (stored_descriptor _ _ _)
      subst d
      exact ⟨old, hold, hview.trans hv⟩
  · constructor
    · rintro ⟨d, hd, hv⟩
      exact ⟨d, (other_descriptor_iff m a b new d halign hb hab).mpr hd, hv⟩
    · rintro ⟨d, hd, hv⟩
      exact ⟨d, (other_descriptor_iff m a b new d halign hb hab).mp hd, hv⟩

theorem af_equivalent (ha hd : Bool) (m : Memory) (a : Nat) (d : BitVec 64)
    (halign : a % 8 = 0) (hold : DescAt m a d) :
    Equivalent ha hd m (store m a (S1Descriptor.setAF d)) :=
  store_equivalent ha hd m a d _ halign hold (S1Descriptor.setAF_view ha hd d).symm

theorem dirty_equivalent (m : Memory) (a : Nat) (d : BitVec 64)
    (halign : a % 8 = 0) (hold : DescAt m a d) (hdbm : d.getLsbD 51 = true) :
    Equivalent true true m (store m a (S1Descriptor.setDirty d)) :=
  store_equivalent true true m a d _ halign hold (S1Descriptor.setDirty_view d hdbm).symm

theorem af_observation (ha hd : Bool) (m : Memory) (a : Nat) (d : BitVec 64) :
    Observed ha hd (store m a (S1Descriptor.setAF d)) a (S1Descriptor.view ha hd d) := by
  exact ⟨_, stored_descriptor _ _ _, S1Descriptor.setAF_view ha hd d⟩

theorem dirty_observation (m : Memory) (a : Nat) (d : BitVec 64)
    (hdbm : d.getLsbD 51 = true) :
    Observed true true (store m a (S1Descriptor.setDirty d)) a
      (S1Descriptor.view true true d) := by
  exact ⟨_, stored_descriptor _ _ _, S1Descriptor.setDirty_view d hdbm⟩

#print axioms write_eq
#print axioms other_descriptor
#print axioms af_observation
#print axioms dirty_observation
#print axioms af_equivalent
#print axioms dirty_equivalent
end S1ByteMemory
