import MemM1.MemPair8W
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemPair8V5
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2 MemM1.MemWriteD1
open MemM1.MemWriteD4 MemM1.MemWriteD5 MemM1.MemWriteD6 MemM1.MemWriteD7 MemM1.MemDataV3 MemM1.MemDataV5
open MemM1.MemPair8R MemM1.MemPair8W
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
open ArmCert.Premises.TranslationAgreesV3 (TTWReadsOK DataPins)

/-- E17 v3's event delta for a translation run from ANY state with `s`'s registers and memory
    (not only a framed one): the log grows by translationStart ++ W ++ translationEnd. -/
theorem events_at {m : ConsumerMap} {walk : BitVec 64 → List Nat} {s : State}
    (h : AgreesV3 m walk s) (a : BitVec 64) (acc : AccessDescriptor) (al : Bool) (n : Int)
    (hp : m.permitted a acc al n) (u : State) (hu : u.regs = s.regs) (hum : u.mem = s.mem)
    (ad : AddressDescriptor) (t1 : State)
    (hta : AArch64_TranslateAddress a acc al n u = .ok ad t1) :
    ∃ ti W, t1.events = u.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
      TTWReadsOK walk a W := by
  rcases h u hu hum a acc al n hp with ⟨ad', t', ht, _, _, _, _, _, _, _, _, _, ti, W, hev, hW⟩
  rw [hta] at ht
  injection ht with had ht'
  subst had ht'
  exact ⟨ti, W, hev, hW⟩

/-- E17 v3 gives the read skeleton's per-half premise. -/
theorem tas_of {m : ConsumerMap} {walk : BitVec 64 → List Nat} {s : State}
    (h : AgreesV3 m walk s) (b : BitVec 64) (acc : AccessDescriptor)
    (hp : m.permitted b acc true ((8 : Nat) : Int)) (hif : acc.acctype ≠ .AccessType_IFETCH) :
    TAS b acc (m.pa b) s := by
  intro u hu hum
  rcases h u hu hum b acc true _ hp with ⟨ad, t, ht, hf, hpa, hmt, hin, hout, hv, _, hdata, hm, _⟩
  exact ⟨ad, t, ht, hf, by rw [hpa], hmt, hin, hout, hv, hdata hif, hm⟩

theorem ev_shape (A W1 W2 : Array Event) (s1 e1 x1 s2 e2 x2 : Event) :
    ((A ++ #[s1] ++ W1 ++ #[e1]).push x1 ++ #[s2] ++ W2 ++ #[e2]).push x2 =
      A ++ #[s1] ++ W1 ++ #[e1, x1, s2] ++ W2 ++ #[e2, x2] := by
  apply Array.toList_inj.mp
  simp

/-- The kmap permission for a 16-byte in-page access at an 8-aligned VA gives the two 8-byte
    halves' permissions (same page, `a` and `addInt a 8`). -/
theorem kmap_halves (P : BitVec 64 → Option MemM1.ConsumerV2.Page) (a : BitVec 64)
    (acc : AccessDescriptor) (h : (MemM1.ConsumerV2.kmap P).permitted a acc true ((16 : Nat) : Int)) :
    (MemM1.ConsumerV2.kmap P).permitted a acc true ((8 : Nat) : Int) ∧
      (MemM1.ConsumerV2.kmap P).permitted (BitVec.addInt a ((8 : Nat) : Int)) acc true ((8 : Nat) : Int) := by
  rcases h with ⟨hva, _, hpg, p, hp, hacc⟩
  have hpg' : a.toNat % 4096 + 8 < 4096 := by omega
  have e8 : BitVec.addInt a ((8 : Nat) : Int) = a + BitVec.ofNat 64 8 := addInt8 a
  have hn := MemM1.ConsumerV2.add_toNat a 8 hva hpg'
  have hpage := MemM1.ConsumerV2.add_page a 8 hva hpg'
  refine ⟨⟨hva, by omega, by omega, p, hp, hacc⟩, ?_⟩
  rw [e8]
  refine ⟨by omega, by omega, ?_, p, by rw [hpage]; exact hp, hacc⟩
  rw [hn]
  have : (a.toNat + 8) % 4096 = a.toNat % 4096 + 8 := by omega
  omega

/-- **LDP 64-bit, FEAT_LSE2, VA 8- but not 16-aligned (`Mem_read__1 a 16 acc true`) on E17 v3 +
    DataPins v5.** TWO single-copy 8-byte reads, each with its own translation: events =
    `start ti1 ++ W1 ++ end ad1 ++ memRead (m.pa a) 8 (some a)`, then
    `start ti2 ++ W2 ++ end ad2 ++ memRead (m.pa (a+8)) 8 (some (a+8))`. Value = the 16 bytes LE
    (bytes 0..7 at m.pa a = first register, bytes 8..15 at m.pa (a+8)). -/
theorem readV5_ldp8 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp1 : m.permitted a acc true ((8 : Nat) : Int))
    (hp2 : m.permitted (BitVec.addInt a ((8 : Nat) : Int)) acc true ((8 : Nat) : Int))
    (hio1 : NotMMIO (m.pa a)) (hio2 : NotMMIO (m.pa (BitVec.addInt a ((8 : Nat) : Int))))
    (data : BitVec (16 * 8))
    (hm1 : ∀ i < 8, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8))
    (hm2 : ∀ i < 8, s.mem[(m.pa (BitVec.addInt a ((8 : Nat) : Int))).toNat + i]? =
      some (data.extractLsb' (8 * (i + 8)) 8)) :
    ∃ ad1 ti1 W1 ad2 ti2 W2 t, Mem_read__1 a 16 acc true s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti1] ++ W1 ++
        #[Event.translationEnd ad1,
          .memRead (m.pa a).toNat 8 (some a.toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false,
          Event.translationStart ti2] ++ W2 ++
        #[Event.translationEnd ad2,
          .memRead (m.pa (BitVec.addInt a ((8 : Nat) : Int))).toNat 8 (some (BitVec.addInt a ((8 : Nat) : Int)).toNat)
            (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK walk a W1 ∧ TTWReadsOK walk (BitVec.addInt a ((8 : Nat) : Int)) W2 ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  have hif := gpr_not_if hA.gpr
  rcases pair8_read a h8 h16 acc s (m.pa a) (m.pa (BitVec.addInt a ((8 : Nat) : Int))) data hA
      (postRegs2_v5 s hD hB) hD.lse2 (tas_of hT a acc hp1 hif) (tas_of hT _ acc hp2 hif) hio1 hio2
      hm1 hm2 with
    ⟨u1, ad1, t11, x, u2, ad2, t21, t, fu1, h1, evx, rx, mx, fu2, h2, h, evt, rt, mt⟩
  rcases events_at hT a acc true _ hp1 u1 fu1.1 fu1.2.1 ad1 t11 h1 with ⟨ti1, W1, ev1, hW1⟩
  rcases events_at hT _ acc true _ hp2 u2 (fu2.1.trans rx) (fu2.2.1.trans mx) ad2 t21 h2 with
    ⟨ti2, W2, ev2, hW2⟩
  refine ⟨ad1, ti1, W1, ad2, ti2, W2, t, h, ?_, hW1, hW2, rt, mt⟩
  rw [evt, ev2, fu2.2.2, evx, ev1, fu1.2.2, ev_shape]

/-- E17 v3 at the state after the first half's write (the second translation runs there). E17 v3 is
    a per-state premise closed only over states with `s`'s memory, so for a two-access store it has
    to be supplied at the post-first-write memory (or by a run-level E17 closed under data writes
    to non-table bytes). -/
def AgreesAfter (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State) (pa : BitVec 56)
    (g : Nat → BitVec 8) : Prop :=
  ∀ s1 : State, s1.regs = s.regs → s1.mem = wfold s.mem pa.toNat 8 g → AgreesV3 m walk s1

/-- **STP 64-bit, FEAT_LSE2, VA 8- but not 16-aligned (`Mem_set__1 a 16 acc true v`) on E17 v3 +
    DataPins v5 (+ E17 v3 at the post-first-write state).** TWO single-copy 8-byte writes, each with
    its own translation: events = `start ti1 ++ W1 ++ end ad1 ++ memWrite (m.pa a) 8 (some a)
    (bytes 0..7 of v)`, then `start ti2 ++ W2 ++ end ad2 ++ memWrite (m.pa (a+8)) 8 (some (a+8))
    (bytes 8..15)`. Registers unchanged; memory = both 8-byte writes. -/
theorem stpV5_8 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (v : BitVec (16 * 8)) (hA : AccDWT acc)
    (hp1 : m.permitted a acc true ((8 : Nat) : Int))
    (hp2 : m.permitted (BitVec.addInt a ((8 : Nat) : Int)) acc true ((8 : Nat) : Int))
    (hio1 : NotMMIO (m.pa a)) (hio2 : NotMMIO (m.pa (BitVec.addInt a ((8 : Nat) : Int))))
    (hT2 : AgreesAfter m walk s (m.pa a) (fun j => v.extractLsb' (8 * j) 8)) :
    ∃ ad1 ti1 W1 ad2 ti2 W2 t, Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti1] ++ W1 ++
        #[Event.translationEnd ad1,
          .memWrite (m.pa a).toNat 8 (some a.toNat) akPlain (some (v.extractLsb' 0 64)) none,
          Event.translationStart ti2] ++ W2 ++
        #[Event.translationEnd ad2,
          .memWrite (m.pa (BitVec.addInt a ((8 : Nat) : Int))).toNat 8
            (some (BitVec.addInt a ((8 : Nat) : Int)).toNat) akPlain (some (v.extractLsb' 64 64)) none] ∧
      TTWReadsOK walk a W1 ∧ TTWReadsOK walk (BitVec.addInt a ((8 : Nat) : Int)) W2 ∧
      t.regs = s.regs ∧
      t.mem = wfold (wfold s.mem (m.pa a).toNat 8 (fun j => v.extractLsb' (8 * j) 8))
        (m.pa (BitVec.addInt a ((8 : Nat) : Int))).toNat 8 (fun j => v.extractLsb' (8 * (j + 8)) 8) := by
  have hif := gpr_not_if hA.base.gpr
  rcases pair8_set a h8 h16 acc s v hA (m.pa a) (m.pa (BitVec.addInt a ((8 : Nat) : Int)))
      (preW_v5 acc s hD hB) hD.spe hD.lse2 (strongTA_of hT a acc 8 hp1 hif)
      (fun s1 hr hm => strongTA_of (hT2 s1 hr hm) _ acc 8 hp2 hif) hio1 hio2 with
    ⟨u1, ad1, t11, x, u2, ad2, t21, t, fu1, h1, evx, rx, mx, fu2, h2, h, evt, rt, mt⟩
  rcases events_at hT a acc true _ hp1 u1 fu1.1 fu1.2.1 ad1 t11 h1 with ⟨ti1, W1, ev1, hW1⟩
  rcases events_at (hT2 x rx mx) _ acc true _ hp2 u2 fu2.1 fu2.2.1 ad2 t21 h2 with
    ⟨ti2, W2, ev2, hW2⟩
  refine ⟨ad1, ti1, W1, ad2, ti2, W2, t, h, ?_, hW1, hW2, rt, by rw [mt, mx]⟩
  rw [evt, ev2, fu2.2.2, evx, ev1, fu1.2.2, ev_shape]

#print axioms events_at
#print axioms tas_of
#print axioms ev_shape
#print axioms kmap_halves
#print axioms readV5_ldp8
#print axioms stpV5_8
end MemM1.MemPair8V5
