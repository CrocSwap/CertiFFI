import MemM1.MemPair8V5
import MemM1.MemInv
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.PairAfter
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.MemReadIF MemM1.MemReadD2 MemM1.MemWriteD1 MemM1.MemWriteD4 MemM1.MemWriteD5
open MemM1.MemDataV3 MemM1.MemDataV5 MemM1.MemPair8R MemM1.MemPair8V5 MemM1.MemInv
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
open ArmCert.Premises.TranslationAgreesV3 (TTWReadsOK DataPins)
open MemM1.ConsumerV2 (Page)
open MemM1.ConsumerB (kmapB walkB)

/-- **AgreesAfter from memory's run invariant.** An 8-byte write at the PA of a permitted 8-byte
    access changes only consumer-mapped bytes, so it preserves `UnmappedSame` (and registers are
    unchanged), hence `MemInv`, hence E17 v3 at the post-write state. -/
theorem agreesAfter_of_memInv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop)
    (s : State) (h : MemInv s0 P4 P2 TB s) (a : BitVec 64) (acc : AccessDescriptor)
    (hp : (kmapB P4 P2).permitted a acc true ((8 : Nat) : Int)) (g : Nat → BitVec 8) :
    AgreesAfter (kmapB P4 P2) (walkB s0.regs s0.mem P2) s ((kmapB P4 P2).pa a) g := by
  intro s1 hr hm
  have hU : UnmappedSame (kmapB P4 P2) s s1 :=
    unmapped_of (kmapB P4 P2) h.1.mapOK a acc 8 hp s s1 g (fun p _ => by rw [hm, wfold_get])
  have hsys : MemM1.StepInv2.SysEq2 s.regs s1.regs := by
    rw [hr]; exact MemM1.StepInv2.SysEq2.refl _
  exact (memInv_agrees s0 P4 P2 TB s1 (memInv_step s0 P4 P2 TB s s1 h hsys hU)).1

/-- The kmapB permission for a 16-byte access at an 8-aligned VA gives both 8-byte halves'
    permissions (same 2 MB block, or same 4 KB page). -/
theorem kmapB_halves (P4 P2 : BitVec 64 → Option Page) (a : BitVec 64) (acc : AccessDescriptor)
    (h : (kmapB P4 P2).permitted a acc true ((16 : Nat) : Int)) :
    (kmapB P4 P2).permitted a acc true ((8 : Nat) : Int) ∧
      (kmapB P4 P2).permitted (BitVec.addInt a ((8 : Nat) : Int)) acc true ((8 : Nat) : Int) := by
  rcases h with ⟨hva, _, hrest⟩
  have e8 : BitVec.addInt a ((8 : Nat) : Int) = a + BitVec.ofNat 64 8 := addInt8 a
  rcases hrest with ⟨b, h2, hblk, hacc⟩ | ⟨h2, hpg, p, h4, hacc⟩
  · have hi : a.toNat % 2097152 + 8 < 2097152 := by omega
    have hn : (a + BitVec.ofNat 64 8).toNat = a.toNat + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hblk' := MemM1.ConsumerB.add_block a 8 hva hi
    refine ⟨⟨hva, by omega, Or.inl ⟨b, h2, by omega, hacc⟩⟩, ?_⟩
    rw [e8]
    refine ⟨by omega, by omega, Or.inl ⟨b, by rw [hblk']; exact h2, ?_, hacc⟩⟩
    rw [hn]; omega
  · have hi : a.toNat % 4096 + 8 < 4096 := by omega
    have hn := MemM1.ConsumerV2.add_toNat a 8 hva hi
    have hpage := MemM1.ConsumerV2.add_page a 8 hva hi
    have hi2 : a.toNat % 2097152 + 8 < 2097152 := by omega
    have hblk' := MemM1.ConsumerB.add_block a 8 hva hi2
    refine ⟨⟨hva, by omega, Or.inr ⟨h2, by omega, p, h4, hacc⟩⟩, ?_⟩
    rw [e8]
    refine ⟨by omega, by omega, Or.inr ⟨by rw [hblk']; exact h2, ?_, p, by rw [hpage]; exact h4, hacc⟩⟩
    rw [hn]; omega

/-- **STP 64-bit, LSE2, 8- but not 16-aligned, on memory's run invariant.** -/
theorem stpV5_8_inv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (hI : MemInv s0 P4 P2 TB s) (hB : BEPins s.regs)
    (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (v : BitVec (16 * 8)) (hA : AccDWT acc)
    (hp : (kmapB P4 P2).permitted a acc true ((16 : Nat) : Int))
    (hio1 : NotMMIO ((kmapB P4 P2).pa a))
    (hio2 : NotMMIO ((kmapB P4 P2).pa (BitVec.addInt a ((8 : Nat) : Int)))) :
    ∃ ad1 ti1 W1 ad2 ti2 W2 t, Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti1] ++ W1 ++
        #[Event.translationEnd ad1,
          .memWrite ((kmapB P4 P2).pa a).toNat 8 (some a.toNat) akPlain (some (v.extractLsb' 0 64)) none,
          Event.translationStart ti2] ++ W2 ++
        #[Event.translationEnd ad2,
          .memWrite ((kmapB P4 P2).pa (BitVec.addInt a ((8 : Nat) : Int))).toNat 8
            (some (BitVec.addInt a ((8 : Nat) : Int)).toNat) akPlain (some (v.extractLsb' 64 64)) none] ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) a W1 ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) (BitVec.addInt a ((8 : Nat) : Int)) W2 ∧
      t.regs = s.regs ∧
      t.mem = wfold (wfold s.mem ((kmapB P4 P2).pa a).toNat 8 (fun j => v.extractLsb' (8 * j) 8))
        ((kmapB P4 P2).pa (BitVec.addInt a ((8 : Nat) : Int))).toNat 8
        (fun j => v.extractLsb' (8 * (j + 8)) 8) := by
  rcases memInv_agrees s0 P4 P2 TB s hI with ⟨hT, _, hD⟩
  rcases kmapB_halves P4 P2 a acc hp with ⟨hp1, hp2⟩
  exact stpV5_8 _ _ s hT hD hB a h8 h16 acc v hA hp1 hp2 hio1 hio2
    (agreesAfter_of_memInv s0 P4 P2 TB s hI a acc hp1 _)

/-- **LDP 64-bit, LSE2, 8- but not 16-aligned, on memory's run invariant.** -/
theorem readV5_ldp8_inv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (hI : MemInv s0 P4 P2 TB s) (hB : BEPins s.regs)
    (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : (kmapB P4 P2).permitted a acc true ((16 : Nat) : Int))
    (hio1 : NotMMIO ((kmapB P4 P2).pa a))
    (hio2 : NotMMIO ((kmapB P4 P2).pa (BitVec.addInt a ((8 : Nat) : Int))))
    (data : BitVec (16 * 8))
    (hm1 : ∀ i < 8, s.mem[((kmapB P4 P2).pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8))
    (hm2 : ∀ i < 8, s.mem[((kmapB P4 P2).pa (BitVec.addInt a ((8 : Nat) : Int))).toNat + i]? =
      some (data.extractLsb' (8 * (i + 8)) 8)) :
    ∃ ad1 ti1 W1 ad2 ti2 W2 t, Mem_read__1 a 16 acc true s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti1] ++ W1 ++
        #[Event.translationEnd ad1,
          .memRead ((kmapB P4 P2).pa a).toNat 8 (some a.toNat)
            (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false,
          Event.translationStart ti2] ++ W2 ++
        #[Event.translationEnd ad2,
          .memRead ((kmapB P4 P2).pa (BitVec.addInt a ((8 : Nat) : Int))).toNat 8
            (some (BitVec.addInt a ((8 : Nat) : Int)).toNat)
            (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) a W1 ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) (BitVec.addInt a ((8 : Nat) : Int)) W2 ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  rcases memInv_agrees s0 P4 P2 TB s hI with ⟨hT, _, hD⟩
  rcases kmapB_halves P4 P2 a acc hp with ⟨hp1, hp2⟩
  exact readV5_ldp8 _ _ s hT hD hB a h8 h16 acc hA hp1 hp2 hio1 hio2 data hm1 hm2

/-- **LDRB on memory's run invariant.** -/
theorem readV5_ldrb_inv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (hI : MemInv s0 P4 P2 TB s) (hB : BEPins s.regs)
    (a : BitVec 64) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : (kmapB P4 P2).permitted a acc true ((1 : Nat) : Int)) (hio : NotMMIO ((kmapB P4 P2).pa a))
    (data : BitVec (1 * 8))
    (hmem : ∀ i < 1, s.mem[((kmapB P4 P2).pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad ti W t, Mem_read a 1 acc s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead ((kmapB P4 P2).pa a).toNat 1 (some a.toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) a W ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  rcases memInv_agrees s0 P4 P2 TB s hI with ⟨hT, _, hD⟩
  exact readV5_ldrb _ _ s hT hD hB a acc hA hp hio data hmem

/-- **LDP 64-bit, LSE2, 16-aligned (one 16-byte access) on memory's run invariant.** -/
theorem readV5_ldp_inv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (hI : MemInv s0 P4 P2 TB s) (hB : BEPins s.regs)
    (a : BitVec 64) (halign : a.toNat % 16 = 0) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : (kmapB P4 P2).permitted a acc true ((16 : Nat) : Int)) (hio : NotMMIO ((kmapB P4 P2).pa a))
    (data : BitVec (16 * 8))
    (hmem : ∀ i < 16, s.mem[((kmapB P4 P2).pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad ti W t, Mem_read__1 a 16 acc true s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead ((kmapB P4 P2).pa a).toNat 16 (some a.toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) a W ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  rcases memInv_agrees s0 P4 P2 TB s hI with ⟨hT, _, hD⟩
  exact readV5_ldp _ _ s hT hD hB a halign acc hA hp hio data hmem

/-- **STRB on memory's run invariant.** -/
theorem strbV5_inv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (hI : MemInv s0 P4 P2 TB s) (hB : BEPins s.regs)
    (a : BitVec 64) (acc : AccessDescriptor) (v : BitVec (1 * 8)) (hA : AccDWT acc)
    (hp : (kmapB P4 P2).permitted a acc true ((1 : Nat) : Int)) (hio : NotMMIO ((kmapB P4 P2).pa a)) :
    ∃ ad ti W t, Mem_set a 1 acc v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite ((kmapB P4 P2).pa a).toNat 1 (some a.toNat) akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 1) v)) none] ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) a W ∧ t.regs = s.regs ∧
      t.mem = wfold s.mem ((kmapB P4 P2).pa a).toNat 1 (wbyte v) ∧
      (∀ p, t.mem[p]? = if ((kmapB P4 P2).pa a).toNat ≤ p ∧ p < ((kmapB P4 P2).pa a).toNat + 1
        then some (wbyte v (p - ((kmapB P4 P2).pa a).toNat)) else s.mem[p]?) := by
  rcases memInv_agrees s0 P4 P2 TB s hI with ⟨hT, _, hD⟩
  exact strbV5 _ _ s hT hD hB a acc v hA hp hio

/-- **STP 64-bit, LSE2, 16-aligned (one 16-byte access) on memory's run invariant.** -/
theorem stpV5_inv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (hI : MemInv s0 P4 P2 TB s) (hB : BEPins s.regs)
    (a : BitVec 64) (ha : a.toNat % 16 = 0) (acc : AccessDescriptor) (v : BitVec (16 * 8))
    (hA : AccDWT acc)
    (hp : (kmapB P4 P2).permitted a acc true ((16 : Nat) : Int)) (hio : NotMMIO ((kmapB P4 P2).pa a)) :
    ∃ ad ti W t, Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite ((kmapB P4 P2).pa a).toNat 16 (some a.toNat) akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) v)) none] ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) a W ∧ t.regs = s.regs ∧
      t.mem = wfold s.mem ((kmapB P4 P2).pa a).toNat 16 (wbyte v) ∧
      (∀ p, t.mem[p]? = if ((kmapB P4 P2).pa a).toNat ≤ p ∧ p < ((kmapB P4 P2).pa a).toNat + 16
        then some (wbyte v (p - ((kmapB P4 P2).pa a).toNat)) else s.mem[p]?) := by
  rcases memInv_agrees s0 P4 P2 TB s hI with ⟨hT, _, hD⟩
  exact stpV5 _ _ s hT hD hB a ha acc v hA hp hio

#print axioms agreesAfter_of_memInv
#print axioms kmapB_halves
#print axioms stpV5_8_inv
#print axioms readV5_ldp8_inv
#print axioms readV5_ldrb_inv
#print axioms readV5_ldp_inv
#print axioms strbV5_inv
#print axioms stpV5_inv
end MemM1.PairAfter
