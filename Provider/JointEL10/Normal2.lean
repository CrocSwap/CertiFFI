import JointEL10.Normal
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.JointSAT.J3b
open S1OuterSetup S1LogicalReference GuestSetup ArmCert.Eval.JointSAT

/- J3': normal-path table whose leaf grants EL0 read/write.
   Four separate tables at k * 0x101000000 (k = 1..4), page at 5 * 0x101000000.
   L0..L2 entries: table descriptors; L3 entry: page descriptor with AP[7:6]=01
   (EL0 RW + privileged RW), AF=1, AttrIndx 0 (MAIR attr0 = 0xff Normal WB),
   GP bit 50 (harmless for data), bit 62 PBHA (ignored: TCR HWU = 0). Every
   descriptor is a byte palindrome, so it encodes the same value under either
 endianness (wp.ee stays symbolic). Same labels as J3 (a design decision). -/
def B1 : Nat := 0x101000000
def B2 : Nat := 0x202000000
def B3 : Nat := 0x303000000
def B4 : Nat := 0x404000000
def d1 : BitVec 64 := 0x0300000202000003#64
def d2 : BitVec 64 := 0x0300000303000003#64
def d3 : BitVec 64 := 0x0300000404000003#64
def leaf : BitVec 64 := 0x4304000505000443#64

theorem palin (d : BitVec 64) (hd : d = d1 ∨ d = d2 ∨ d = d3 ∨ d = leaf)
    (i : Nat) (hi : i < 8) : byte true d i = byte false d i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hd with rfl|rfl|rfl|rfl <;>
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def put (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((m.insert (a + 0) (byte false d 0)).insert (a + 1) (byte false d 1)).insert
    (a + 2) (byte false d 2)).insert (a + 3) (byte false d 3)).insert
    (a + 4) (byte false d 4)).insert (a + 5) (byte false d 5)).insert
    (a + 6) (byte false d 6)).insert (a + 7) (byte false d 7))

def load (m : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  put (put (put (put m B1 d1) B2 d2) B3 d3) B4 leaf

theorem put_same (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec 64) (i : Nat)
    (hi : i < 8) : (put m a d)[a + i]? = some (byte false d i) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [put, Std.ExtHashMap.getElem?_insert, beq_iff_eq] <;> simp

theorem put_other (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec 64) (x : Nat)
    (hx : x < a ∨ a + 8 ≤ x) : (put m a d)[x]? = m[x]? := by
  simp only [put, Std.ExtHashMap.getElem?_insert, beq_iff_eq, Nat.add_zero]
  have h0 : ¬ a = x := by omega
  have h1 : ¬ a + 1 = x := by omega
  have h2 : ¬ a + 2 = x := by omega
  have h3 : ¬ a + 3 = x := by omega
  have h4 : ¬ a + 4 = x := by omega
  have h5 : ¬ a + 5 = x := by omega
  have h6 : ¬ a + 6 = x := by omega
  have h7 : ¬ a + 7 = x := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

theorem load_get (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec 64)
    (hs : (a = B1 ∧ d = d1) ∨ (a = B2 ∧ d = d2) ∨ (a = B3 ∧ d = d3) ∨ (a = B4 ∧ d = leaf))
    (i : Nat) (hi : i < 8) : (load m)[a + i]? = some (byte false d i) := by
  unfold load
  rcases hs with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
  · rw [put_other _ _ _ _ (by unfold B4 B1; omega), put_other _ _ _ _ (by unfold B3 B1; omega),
      put_other _ _ _ _ (by unfold B2 B1; omega), put_same _ _ _ _ hi]
  · rw [put_other _ _ _ _ (by unfold B4 B2; omega), put_other _ _ _ _ (by unfold B3 B2; omega),
      put_same _ _ _ _ hi]
  · rw [put_other _ _ _ _ (by unfold B4 B3; omega), put_same _ _ _ _ hi]
  · rw [put_same _ _ _ _ hi]

def phys (a : Nat) : FullAddress := {paspace := .PAS_NonSecure, address := BitVec.ofNat 56 a}

theorem phys_toNat (a : Nat) (h : a < 2 ^ 56) : (phys a).address.toNat = a := by
  simp [phys, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Loader step (EL2&0 lower range): table bytes plus TTBR0_EL2/HTTBR = B1. -/
def prep20 (s : State) : State :=
  {s with mem := load s.mem,
          regs := (Regs.ref_BitVec_128 ._TTBR0_EL2).set (BitVec.ofNat 128 B1)
            ((Regs.ref_BitVec_64 .HTTBR).set (BitVec.ofNat 64 B1) s.regs)}

/-- Loader step (EL1&0 lower range): table bytes plus TTBR0_EL1/TTBR0_NS = B1. -/
def prep10 (s : State) : State :=
  {s with mem := load s.mem,
          regs := (Regs.ref_BitVec_128 ._TTBR0_EL1).set (BitVec.ofNat 128 B1)
            ((Regs.ref_BitVec_64 .TTBR0_NS).set (BitVec.ofNat 64 B1) s.regs)}

theorem prep20_facts (s : State) :
    (prep20 s).regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled ∧
    (prep20 s).mem = load s.mem ∧
    (prep20 s).regs.bank_BitVec_128 ._TTBR0_EL2 = BitVec.ofNat 128 B1 ∧
    (prep20 s).regs.bank_BitVec_64 .HTTBR = BitVec.ofNat 64 B1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [prep20, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]
  · dsimp only [prep20]
  · simp [prep20, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]
  · simp [prep20, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]

theorem prep10_facts (s : State) :
    (prep10 s).regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled ∧
    (prep10 s).mem = load s.mem ∧
    (prep10 s).regs.bank_BitVec_128 ._TTBR0_EL1 = BitVec.ofNat 128 B1 ∧
    (prep10 s).regs.bank_BitVec_64 .TTBR0_NS = BitVec.ofNat 64 B1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [prep10, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]
  · dsimp only [prep10]
  · simp [prep10, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]
  · simp [prep10, Regs.ref_BitVec_64, Regs.ref_BitVec_128, RegMap.set]

/-- The table data, over memory `mem` containing `load`, for walk parameters
    pie/ha/hd/ee: observation, availability, identity, realization and the
    logical path from root B1 at VA 0 to the level-3 page entry at B4. -/
theorem tables (pie ha hd ee : Bool) (mem : Std.ExtHashMap Nat (BitVec 8))
    (hmem : ∀ a d, ((a = B1 ∧ d = d1) ∨ (a = B2 ∧ d = d2) ∨ (a = B3 ∧ d = d3) ∨
      (a = B4 ∧ d = leaf)) → ∀ i, i < 8 → mem[a + i]? = some (byte false d i))
    (b0 : BitVec 48) (hb0 : b0 = BitVec.ofNat 48 B1) :
    ∃ observe : Observation,
      Available observe (fun p => S2TableRAM.OrdinaryRAM p.address) ∧
      Realizes observe ee pie ha hd (fun a => mem[a]?) ∧
      S1EntryPathSlots.Identity observe ∧
      Path observe 48 0#64 0 9 b0
        (.leaf 3 B4 (phys B4) (S1DescriptorPIE.view pie ha hd leaf)) := by
  let v := fun (d : BitVec 64) => S1DescriptorPIE.view pie ha hd d
  let observe : Observation := fun l p w =>
    (l = B1 ∧ p = phys B1 ∧ w = v d1) ∨ (l = B2 ∧ p = phys B2 ∧ w = v d2) ∨
    (l = B3 ∧ p = phys B3 ∧ w = v d3) ∨ (l = B4 ∧ p = phys B4 ∧ w = v leaf)
  have hst : ∀ d, (v d).stable = S1Descriptor.stable d := fun _ => rfl
  have cb1 : childBase (v d1) = BitVec.ofNat 48 B2 := by unfold childBase; rw [hst]; decide
  have cb2 : childBase (v d2) = BitVec.ofNat 48 B3 := by unfold childBase; rw [hst]; decide
  have cb3 : childBase (v d3) = BitVec.ofNat 48 B4 := by unfold childBase; rw [hst]; decide
  have e : ∀ b l, b < 2 ^ 48 → entryAddress (BitVec.ofNat 48 b) 0#64 l 9 = b := by
    intro b l hb; simp [entryAddress, entryIndex, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  refine ⟨observe, ?_, ?_, ?_, ?_⟩
  · rintro l p w (⟨rfl, rfl, rfl⟩|⟨rfl, rfl, rfl⟩|⟨rfl, rfl, rfl⟩|⟨rfl, rfl, rfl⟩) <;>
      refine ⟨by decide, by decide, ?_⟩ <;>
      (show S2TableRAM.OrdinaryRAM (phys _).address; unfold S2TableRAM.OrdinaryRAM; decide)
  · rintro l p w h
    have key : ∀ a d, ((a = B1 ∧ d = d1) ∨ (a = B2 ∧ d = d2) ∨ (a = B3 ∧ d = d3) ∨
        (a = B4 ∧ d = leaf)) → p = phys a → w = v d →
        ∃ d', BytesAt ee (fun a => mem[a]?) p d' ∧ S1DescriptorPIE.view pie ha hd d' = w := by
      intro a d hs hp hw
      refine ⟨d, ?_, hw.symm⟩
      intro i hi
      have ha56 : a < 2 ^ 56 := by
        rcases hs with ⟨rfl, -⟩|⟨rfl, -⟩|⟨rfl, -⟩|⟨rfl, -⟩ <;> decide
      show mem[p.address.toNat + i]? = some (byte ee d i)
      rw [hp, phys_toNat a ha56, hmem a d hs i hi]
      have hd : d = d1 ∨ d = d2 ∨ d = d3 ∨ d = leaf := by
        rcases hs with ⟨-, h⟩|⟨-, h⟩|⟨-, h⟩|⟨-, h⟩ <;> simp [h]
      cases ee
      · rfl
      · rw [palin d hd i hi]
    rcases h with ⟨-, hp, hw⟩|⟨-, hp, hw⟩|⟨-, hp, hw⟩|⟨-, hp, hw⟩
    · exact key B1 d1 (Or.inl ⟨rfl, rfl⟩) hp hw
    · exact key B2 d2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hp hw
    · exact key B3 d3 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hp hw
    · exact key B4 leaf (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hp hw
  · rintro l p w (⟨rfl, rfl, -⟩|⟨rfl, rfl, -⟩|⟨rfl, rfl, -⟩|⟨rfl, rfl, -⟩) <;> decide
  · subst hb0
    have k3 : descriptorKind 3 (v leaf).stable = .ok .leaf := by rw [hst]; rfl
    have kt : ∀ d l, (d = d1 ∨ d = d2 ∨ d = d3) → l < 3 →
        descriptorKind l (v d).stable = .ok .table := by
      intro d l hd hl; rw [hst]
      have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
      rcases hd with rfl|rfl|rfl <;> rcases this with rfl|rfl|rfl <;> rfl
    have p3 : Path observe 48 0#64 3 9 (BitVec.ofNat 48 B4)
        (.leaf 3 B4 (phys B4) (v leaf)) := by
      have h := Path.leaf (observe := observe) (paBits := 48) (va := 0#64) 3 9
        (BitVec.ofNat 48 B4) (phys B4) (v leaf) (by decide)
        (by rw [e _ _ (by decide)]; decide)
        (by rw [e _ _ (by decide)]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) k3
      rw [e _ _ (by decide)] at h; exact h
    have p2 : Path observe 48 0#64 2 9 (BitVec.ofNat 48 B3) (.leaf 3 B4 (phys B4) (v leaf)) := by
      have h := Path.table (observe := observe) (paBits := 48) (va := 0#64) 2 9
        (BitVec.ofNat 48 B3) (phys B3) (v d3) _ (by decide)
        (by rw [e _ _ (by decide)]; decide)
        (by rw [e _ _ (by decide)]; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
        (kt d3 2 (by simp) (by decide)) (by rw [cb3, e _ _ (by decide)]; decide)
        (by rw [cb3]; exact p3)
      exact h
    have p1 : Path observe 48 0#64 1 9 (BitVec.ofNat 48 B2) (.leaf 3 B4 (phys B4) (v leaf)) :=
      Path.table (observe := observe) (paBits := 48) (va := 0#64) 1 9
        (BitVec.ofNat 48 B2) (phys B2) (v d2) _ (by decide)
        (by rw [e _ _ (by decide)]; decide)
        (by rw [e _ _ (by decide)]; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
        (kt d2 1 (by simp) (by decide)) (by rw [cb2, e _ _ (by decide)]; decide)
        (by rw [cb2]; exact p2)
    exact Path.table (observe := observe) (paBits := 48) (va := 0#64) 0 9
        (BitVec.ofNat 48 B1) (phys B1) (v d1) _ (by decide)
        (by rw [e _ _ (by decide)]; decide)
        (by rw [e _ _ (by decide)]; exact Or.inl ⟨rfl, rfl, rfl⟩)
        (kt d1 0 (by simp) (by decide)) (by rw [cb1, e _ _ (by decide)]; decide)
        (by rw [cb1]; exact p1)


theorem load_mem (m : Std.ExtHashMap Nat (BitVec 8)) : ∀ a d, ((a = B1 ∧ d = d1) ∨
    (a = B2 ∧ d = d2) ∨ (a = B3 ∧ d = d3) ∨ (a = B4 ∧ d = leaf)) → ∀ i, i < 8 →
    (load m)[a + i]? = some (byte false d i) :=
  fun a d hs i hi => load_get m a d hs i hi



#print axioms load_get
#print axioms tables
end ArmCert.Eval.JointSAT.J3b
