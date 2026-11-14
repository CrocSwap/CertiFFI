-- lrSaved, the exit stack-slot round trip.
-- LrField: X19/X30 at their entry values up to the prologue STP (k = 11), the saved pair in the
-- stack slot [entry SP − 16, +16) from k = 12 to the epilogue LDP (k = 354), and X30 back at its
-- entry value from k = 355 to the RET (k = 357). Carry lemmas take the per-step facts Core's v4
-- steps already have (fin.mem = s.mem / WritesOnly + exact D_e / Holds (upds k)); the two value
-- steps take the STP and LDP payloads. No step machinery is imported beyond the plan tables.
import HeapV2StepCerts.MemStepsV3
open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft (NativeState)
open HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace RtSaved

/-- The prologue STP's plan access (k = 11, entry SP − 16, 16 bytes, write). -/
def slotEntry : Nat × Nat × Int × Nat × Bool := (11, 0, -16, 16, true)

/-- The stack slot's VA: entry SP − 16 (= SP + 48 after the prologue's SP −= 64). -/
def slotVA (p : HeapV2E17.Pins) : BitVec 64 := HeapV2E17.dataVA p slotEntry

/-- Byte i of the saved pair, little-endian (x19 at +0, x30 at +8), as STP writes it. -/
def slotByte (v19 v30 : BitVec 64) (i : Nat) : BitVec 8 := (BitVec.append v30 v19).extractLsb' (8 * i) 8

/-- The slot's 16 physical bytes hold the saved pair. -/
def SlotHolds (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (v19 v30 : BitVec 64)
    (x : NativeState) : Prop :=
  ∀ n, mapping (slotVA p) = some n → ∀ i < 16, x.mem[n + i]? = some (slotByte v19 v30 i)

/-- The lrSaved field of ChainInv v4 at plan step k (v19/v30: the entry X19/X30). -/
structure LrField (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (v19 v30 : BitVec 64)
    (k : Nat) (x : NativeState) : Prop where
  low : k ≤ 11 → x.regs.gpr[19] = v19 ∧ x.regs.gpr[30] = v30
  slot : 11 < k → k ≤ 354 → SlotHolds p mapping v19 v30 x
  high : 354 < k → x.regs.gpr[30] = v30

/-! ### Plan-table facts (closed `decide` over the upds table). -/

theorem keep_low : ∀ k, k < 11 → updOf (upds k) (.x 19) = .keep ∧ updOf (upds k) (.x 30) = .keep := by
  decide

theorem keep_high' : ∀ j, j < 3 → updOf (upds (355 + j)) (.x 30) = .keep := by
  decide

theorem keep_high : ∀ k, 355 ≤ k → k < 358 → updOf (upds k) (.x 30) = .keep := by
  intro k lo hi
  have h := keep_high' (k - 355) (by omega)
  rwa [show 355 + (k - 355) = k by omega] at h

theorem slot_entry_member : slotEntry ∈ HeapV2Plan.symbolicAccesses := by decide

/-- The epilogue LDP (k = 354) reads exactly the slot. -/
theorem ldp_entry_va (p : HeapV2E17.Pins) : HeapV2E17.dataVA p (354, 0, -16, 16, false) = slotVA p := rfl

theorem kept_reg {us : List (Reg × Upd)} {s fin : NativeState} (holds : Holds us s fin) (i : Fin 31)
    (keep : updOf us (.x i) = .keep) : fin.regs.gpr[i.val] = s.regs.gpr[i.val] := by
  have h := holds (.x i)
  rw [keep] at h
  exact h

/-! ### Seed and consumer. -/

/-- k = 0: the entry state, with v19/v30 its own X19/X30. -/
theorem field_zero (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (entry : NativeState) :
    LrField p mapping (entry.regs.gpr[19]) (entry.regs.gpr[30]) 0 entry :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- At the RET (k = 357): Exit.exit_lands' lrSaved input, in its exact form. -/
theorem lrSaved_of_chain {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {x : NativeState} (field : LrField p mapping v19 v30 357 x) :
    x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = v30 :=
  field.high (by decide)

/-- With the seed's v30: `source.regs.gpr[key 30] = entry.regs.gpr[30]`. -/
theorem lrSaved_entry {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 : BitVec 64}
    {entry x : NativeState} (field : LrField p mapping v19 (entry.regs.gpr[30]) 357 x) :
    x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = entry.regs.gpr[30] :=
  lrSaved_of_chain field

/-! ### Generic carries. -/

/-- Steps strictly inside the slot phase (12 ≤ k ≤ 353): only the slot bytes matter. -/
theorem carry_slot {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {k : Nat} {s fin : NativeState} (lo : 11 < k) (hi : k < 354)
    (frame : ∀ n, mapping (slotVA p) = some n → ∀ i < 16, fin.mem[n + i]? = s.mem[n + i]?)
    (field : LrField p mapping v19 v30 k s) : LrField p mapping v19 v30 (k + 1) fin :=
  ⟨fun h => absurd h (by omega),
   fun _ _ n hn i hi' => (frame n hn i hi').trans (field.slot lo (by omega) n hn i hi'),
   fun h => absurd h (by omega)⟩

/-- Steps outside the slot phase other than 11 and 354 (k < 11 or 355 ≤ k < 358): the upds
table keeps X19/X30 there, so Holds (upds k) carries the registers. -/
theorem carry_regs {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {k : Nat} {s fin : NativeState} (outside : k < 11 ∨ (355 ≤ k ∧ k < 358))
    (holds : Holds (upds k) s fin)
    (field : LrField p mapping v19 v30 k s) : LrField p mapping v19 v30 (k + 1) fin := by
  rcases outside with lo | ⟨hi, top⟩
  · have keep := keep_low k lo
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · exact (kept_reg holds 19 keep.1).trans (field.low (by omega)).1
    · exact (kept_reg holds 30 keep.2).trans (field.low (by omega)).2
  · refine ⟨fun h => absurd h (by omega), fun _ h => absurd h (by omega), fun _ => ?_⟩
    exact (kept_reg holds 30 (keep_high k hi top)).trans (field.high (by omega))

/-- Any step with k ∉ {11, 354}, from its slot-byte frame (inside the slot phase) and its
register update (outside it). -/
theorem carry {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (frame : 11 < k → k < 354 → ∀ n, mapping (slotVA p) = some n → ∀ i < 16, fin.mem[n + i]? = s.mem[n + i]?)
    (holds : (k < 11 ∨ 355 ≤ k) → Holds (upds k) s fin)
    (field : LrField p mapping v19 v30 k s) : LrField p mapping v19 v30 (k + 1) fin := by
  by_cases inside : 11 < k ∧ k < 354
  · exact carry_slot inside.1 inside.2 (frame inside.1 inside.2) field
  · have out : k < 11 ∨ 355 ≤ k := by omega
    exact carry_regs (by omega) (holds out) field

/-! ### Per step class. -/

/-- Class (straight-line) steps: fin.mem = s.mem and Holds (upds k) s fin (plan_step3_class's
entry_class_next_v3 facts). Also BL steps (Core's caller-route action leaves mem unchanged). -/
theorem carry_class {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (mem : fin.mem = s.mem) (holds : (k < 11 ∨ 355 ≤ k) → Holds (upds k) s fin)
    (field : LrField p mapping v19 v30 k s) : LrField p mapping v19 v30 (k + 1) fin :=
  carry top n11 n354 (fun _ _ n _ i _ => by rw [mem]) holds field

/-- Branch steps: memory unchanged and GPRs kept (BranchTailsX / entry_class_next_v3_br). -/
theorem carry_branch {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (mem : fin.mem = s.mem) (gpr : fin.regs.gpr = s.regs.gpr)
    (field : LrField p mapping v19 v30 k s) : LrField p mapping v19 v30 (k + 1) fin := by
  by_cases inside : 11 < k ∧ k < 354
  · exact carry_slot inside.1 inside.2 (fun n _ i _ => by rw [mem]) field
  · refine ⟨fun h => ?_, fun h1 h2 => absurd (And.intro (by omega) (by omega) : 11 < k ∧ k < 354) inside,
      fun h => ?_⟩
    · rw [gpr]; exact field.low (by omega)
    · rw [gpr]; exact field.high (by omega)

/-! ### Memory steps: exact per-entry PA range and the slot separation check. -/

/-- The exact physical bytes of plan access `e`: its mapped range, and for a 16-byte pair also the
range its second half maps to (the `plus8` VA, as the pair tails write it). -/
def accPA (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (e : Nat × Nat × Int × Nat × Bool)
    (y : Nat) : Prop :=
  (∃ n, mapping (HeapV2E17.dataVA p e) = some n ∧ n ≤ y ∧ y < n + e.2.2.2.1) ∨
    (e.2.2.2.1 = 16 ∧ ∃ n, mapping (plus8 (HeapV2E17.dataVA p e)) = some n ∧ n ≤ y ∧ y < n + 8)

/-- Deployment premise: every plan WRITE strictly between the prologue STP and the epilogue LDP
has its PA range(s) disjoint from the slot's. -/
def SlotSep (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Prop :=
  ∀ e ∈ HeapV2Plan.symbolicAccesses, e.2.2.2.2 = true → 11 < e.1 → e.1 < 354 →
    ∀ s, mapping (slotVA p) = some s →
      (∀ n, mapping (HeapV2E17.dataVA p e) = some n → n + e.2.2.2.1 ≤ s ∨ s + 16 ≤ n) ∧
      (e.2.2.2.1 = 16 → ∀ n, mapping (plus8 (HeapV2E17.dataVA p e)) = some n → n + 8 ≤ s ∨ s + 16 ≤ n)

/-- Boolean form of SlotSep (a deployment check, DataStatic-style). -/
def slotSepCheck (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Bool :=
  HeapV2Plan.symbolicAccesses.all fun e =>
    !(e.2.2.2.2 && decide (11 < e.1) && decide (e.1 < 354)) ||
      match mapping (slotVA p) with
      | none => true
      | some s =>
        (match mapping (HeapV2E17.dataVA p e) with
          | some n => decide (n + e.2.2.2.1 ≤ s) || decide (s + 16 ≤ n)
          | none => true) &&
        (e.2.2.2.1 != 16 ||
          match mapping (plus8 (HeapV2E17.dataVA p e)) with
          | some n => decide (n + 8 ≤ s) || decide (s + 16 ≤ n)
          | none => true)

theorem slotSep_of_check {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    (h : slotSepCheck p mapping = true) : SlotSep p mapping := by
  intro e he hw lo hi s hs
  have c := List.all_eq_true.1 h e he
  simp only [hw, Bool.true_and, decide_eq_true lo, decide_eq_true hi, Bool.not_true, Bool.false_or, hs,
    Bool.and_eq_true] at c
  obtain ⟨c1, c2⟩ := c
  refine ⟨fun n hn => ?_, fun h16 n hn => ?_⟩
  · simp only [hn, Bool.or_eq_true, decide_eq_true_eq] at c1; exact c1
  · simp only [h16, bne_self_eq_false, Bool.false_or, hn, Bool.or_eq_true, decide_eq_true_eq] at c2; exact c2

/-- A write's exact PA ranges miss the slot. -/
theorem accPA_sep {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} (sep : SlotSep p mapping)
    {e : Nat × Nat × Int × Nat × Bool} (he : e ∈ HeapV2Plan.symbolicAccesses) (hw : e.2.2.2.2 = true)
    (lo : 11 < e.1) (hi : e.1 < 354) :
    ∀ y, accPA p mapping e y → ∀ s, mapping (slotVA p) = some s → ¬ (s ≤ y ∧ y < s + 16) := by
  intro y hy s hs ⟨h3, h4⟩
  have sp := sep e he hw lo hi s hs
  rcases hy with ⟨n, hn, h1, h2⟩ | ⟨h16, n, hn, h1, h2⟩
  · rcases sp.1 n hn with h | h <;> omega
  · rcases sp.2 h16 n hn with h | h <;> omega

/-- Memory steps: WritesOnly `written` with `written ⊆ D` and `D` off the slot (D := accPA e for
stores, ∅ for loads), plus Holds (upds k) outside the slot phase. -/
theorem carry_mem {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (written D : Nat → Prop) (wo : WritesOnly written (fun y => s.mem[y]?) (fun y => fin.mem[y]?))
    (inD : ∀ y, written y → D y)
    (off : 11 < k → k < 354 → ∀ y, D y → ∀ n, mapping (slotVA p) = some n → ¬ (n ≤ y ∧ y < n + 16))
    (holds : (k < 11 ∨ 355 ≤ k) → Holds (upds k) s fin)
    (field : LrField p mapping v19 v30 k s) : LrField p mapping v19 v30 (k + 1) fin :=
  carry top n11 n354 (fun lo hi n hn i hi' =>
    wo (n + i) (fun w => off lo hi (n + i) (inD _ w) n hn ⟨by omega, by omega⟩)) holds field

/-- Store step k = e.1 inside the slot phase, D := accPA e, from SlotSep. -/
theorem carry_store {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {s fin : NativeState} (sep : SlotSep p mapping)
    {e : Nat × Nat × Int × Nat × Bool} (he : e ∈ HeapV2Plan.symbolicAccesses) (hw : e.2.2.2.2 = true)
    (lo : 11 < e.1) (hi : e.1 < 354)
    (written : Nat → Prop) (wo : WritesOnly written (fun y => s.mem[y]?) (fun y => fin.mem[y]?))
    (inD : ∀ y, written y → accPA p mapping e y)
    (field : LrField p mapping v19 v30 e.1 s) : LrField p mapping v19 v30 (e.1 + 1) fin :=
  carry_mem (by omega) (by omega) (by omega) written (accPA p mapping e) wo inD
    (fun _ _ => accPA_sep sep he hw lo hi) (fun h => absurd h (by omega)) field

/-! ### The two value steps. -/

theorem slotByte_stp (v19 v30 : BitVec 64) (i : Nat) :
    MemM1.MemWriteD4.wbyte (BitVec.cast (by decide : 64 + 64 = 16 * 8) (BitVec.append v30 v19)) i =
      slotByte v19 v30 i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [MemM1.MemWriteD4.wbyte, slotByte, BitVec.getLsbD_extractLsb', Sail.BitVec.castWidth, dite_true,
    BitVec.getLsbD_cast]

/-- k = 11, prologue STP x19, x30, [sp, #48]: its payload at the slot is (X19, X30) of s. -/
theorem carry_stp11 {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {s fin : NativeState}
    (payload : ∀ n, mapping (slotVA p) = some n → ∀ i < 16,
      fin.mem[n + i]? = some (slotByte (s.regs.gpr[19]) (s.regs.gpr[30]) i))
    (field : LrField p mapping v19 v30 11 s) : LrField p mapping v19 v30 12 fin := by
  obtain ⟨h19, h30⟩ := field.low (by decide)
  refine ⟨fun h => absurd h (by decide), fun _ _ n hn i hi => ?_, fun h => absurd h (by decide)⟩
  rw [payload n hn i hi, h19, h30]

theorem ldpHi_append (hi lo : BitVec 64) :
    ArmCertMem.LdpEval.ldpHi (BitVec.cast (by decide : 64 + 64 = 128) (BitVec.append hi lo)) = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [ArmCertMem.LdpEval.ldpHi, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, Sail.BitVec.castWidth,
    dite_true, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast]
  rw [BitVec.append_eq, BitVec.getLsbD_append]
  simp [hi']

/-- k = 354, epilogue LDP x19, x30, [sp, #48]: X30 := the loaded high half. The payload is
stated for every 128-bit value whose bytes sit at the slot (the LDP reads the slot: ldp_entry_va). -/
theorem carry_ldp354 {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {v19 v30 : BitVec 64}
    {s fin : NativeState} (mapped : ∃ n, mapping (slotVA p) = some n)
    (payload : ∀ n, mapping (slotVA p) = some n → ∀ d : BitVec 128,
      (∀ i < 16, s.mem[n + i]? = some (d.extractLsb' (8 * i) 8)) →
      fin.regs.gpr[30] = ArmCertMem.LdpEval.ldpHi d)
    (field : LrField p mapping v19 v30 354 s) : LrField p mapping v19 v30 355 fin := by
  obtain ⟨n, hn⟩ := mapped
  refine ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide), fun _ => ?_⟩
  rw [payload n hn (BitVec.cast (by decide) (BitVec.append v30 v19)) (fun i hi => by
    rw [field.slot (by decide) (by decide) n hn i hi]; rfl)]
  exact ldpHi_append v30 v19

/-- Byte extensionality for 128-bit values (used to identify the LDP's read value). -/
theorem bytes_ext {d d' : BitVec 128} (h : ∀ i < 16, d.extractLsb' (8 * i) 8 = d'.extractLsb' (8 * i) 8) :
    d = d' := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have e : 8 * (j / 8) + j % 8 = j := Nat.div_add_mod j 8
  have := congrArg (fun v => v.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', e, show j % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
    Bool.true_and] at this
  exact this

#print axioms keep_low
#print axioms keep_high
#print axioms slot_entry_member
#print axioms field_zero
#print axioms lrSaved_of_chain
#print axioms lrSaved_entry
#print axioms carry
#print axioms carry_class
#print axioms carry_branch
#print axioms slotSep_of_check
#print axioms carry_mem
#print axioms carry_store
#print axioms slotByte_stp
#print axioms carry_stp11
#print axioms ldpHi_append
#print axioms carry_ldp354
#print axioms bytes_ext
end RtSaved
