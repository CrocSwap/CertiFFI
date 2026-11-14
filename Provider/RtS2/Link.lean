-- LrField v2 = RtSaved.LrField + the callee link. Between each BL
-- (k = 15/150/252) and its helper's RET (k = 146/249/331), X30 holds the BL's return address
-- base + offset of BL+4, which the RET's target needs. Carries reuse LRSaved's (forgetful map);
-- the link is carried by Holds (upds k) (the table keeps X30 on every non-BL step of a link range),
-- started at the BL by its link write, and read at the RET (link_target).
import RtSaved.MemFacts
open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft (NativeState)
open HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 4096
set_option Elab.async false
namespace RtSaved2

/-- Entry-relative return address live in X30 at plan step k (inside a helper call), if any. -/
def linkRet (k : Nat) : Option Nat :=
  if 15 < k ∧ k ≤ 146 then some 0x40 else if 150 < k ∧ k ≤ 249 then some 0x50
  else if 252 < k ∧ k ≤ 331 then some 0x5c else none

/-- The lrSaved field of ChainInv v4, with the helper-call link. -/
structure LrField (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (v19 v30 : BitVec 64) (k : Nat) (x : NativeState) : Prop where
  low : k ≤ 11 → x.regs.gpr[19] = v19 ∧ x.regs.gpr[30] = v30
  slot : 11 < k → k ≤ 354 → RtSaved.SlotHolds p mapping v19 v30 x
  high : 354 < k → x.regs.gpr[30] = v30
  link : ∀ r, linkRet k = some r → x.regs.gpr[30] = base + BitVec.ofNat 64 (0x10278 + r)

variable {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {base v19 v30 : BitVec 64}

theorem LrField.old {k : Nat} {x : NativeState} (f : LrField p mapping base v19 v30 k x) :
    RtSaved.LrField p mapping v19 v30 k x := ⟨f.low, f.slot, f.high⟩

theorem LrField.ofOld {k : Nat} {x : NativeState} (f : RtSaved.LrField p mapping v19 v30 k x)
    (link : ∀ r, linkRet k = some r → x.regs.gpr[30] = base + BitVec.ofNat 64 (0x10278 + r)) :
    LrField p mapping base v19 v30 k x := ⟨f.low, f.slot, f.high, link⟩

/-! ### Plan-table facts (kernel-decided over the upds table). -/

/-- Every non-BL step whose successor is inside a link range is itself inside it and keeps X30. -/
def linkKeepOK (k : Nat) : Bool :=
  k == 15 || k == 150 || k == 252 || (linkRet (k + 1)).isNone ||
    (linkRet (k + 1) == linkRet k && updOf (upds k) (.x 30) == .keep)

theorem linkKeepOK_all : ∀ k, k < 358 → linkKeepOK k = true := by decide +kernel

theorem link_keep (k : Nat) (top : k < 358) (h15 : k ≠ 15) (h150 : k ≠ 150) (h252 : k ≠ 252)
    (some_ : (linkRet (k + 1)).isSome = true) :
    linkRet (k + 1) = linkRet k ∧ updOf (upds k) (.x 30) = .keep := by
  have h := linkKeepOK_all k top
  have hn : (linkRet (k + 1)).isNone = false := by
    cases e : linkRet (k + 1) <;> simp_all
  simp only [linkKeepOK, h15, h150, h252, hn, beq_iff_eq, Bool.false_or, Bool.and_eq_true,
    beq_self_eq_true, decide_false, Bool.or_false] at h
  simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact absurd h h15
  · exact absurd h h150
  · exact absurd h h252
  · simpa only [Bool.and_eq_true, beq_iff_eq] using h

theorem link_none_low : ∀ k, k ≤ 15 → linkRet k = none := by decide
theorem link_none_355 : linkRet 355 = none := by decide
theorem link_none_12 : linkRet 12 = none := by decide

/-! ### Seed, consumers. -/

theorem field_zero (entry : NativeState) :
    LrField p mapping base (entry.regs.gpr[19]) (entry.regs.gpr[30]) 0 entry :=
  LrField.ofOld (RtSaved.field_zero p mapping entry) (fun r h => by simp [linkRet] at h)

theorem lrSaved_of_chain {x : NativeState} (field : LrField p mapping base v19 v30 357 x) :
    x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = v30 :=
  RtSaved.lrSaved_of_chain field.old

/-- At a helper's RET (k = 146 / 249 / 331): X30 is the return address base + offset (k+1). -/
theorem link_target {k : Nat} {x : NativeState} (hk : k = 146 ∨ k = 249 ∨ k = 331)
    (field : LrField p mapping base v19 v30 k x) :
    x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] =
      base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (k + 1) := by
  simp only [show (GPRSummary.key (30#5 : BitVec 5).toNat).val = 30 by decide]
  rcases hk with rfl | rfl | rfl
  · rw [field.link 0x40 (by decide)]
    first | (congr 1; done) | (congr 1; decide +kernel)
  · rw [field.link 0x50 (by decide)]
    first | (congr 1; done) | (congr 1; decide +kernel)
  · rw [field.link 0x5c (by decide)]
    first | (congr 1; done) | (congr 1; decide +kernel)

/-! ### Carries. -/

theorem link_carry {k : Nat} {s fin : NativeState} (top : k < 358) (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252)
    (holds : Holds (upds k) s fin) (field : LrField p mapping base v19 v30 k s) :
    ∀ r, linkRet (k + 1) = some r → fin.regs.gpr[30] = base + BitVec.ofNat 64 (0x10278 + r) := by
  intro r hr
  obtain ⟨same, keep⟩ := link_keep k top nBL.1 nBL.2.1 nBL.2.2 (by rw [hr]; rfl)
  have k30 : fin.regs.gpr[30] = s.regs.gpr[30] := RtSaved.kept_reg holds 30 keep
  rw [k30]
  exact field.link r (same ▸ hr)

/-- Any step with k ∉ {11, 354, 15, 150, 252}: slot-byte frame inside the slot phase, Holds (upds k). -/
theorem carry {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252)
    (frame : 11 < k → k < 354 → ∀ n, mapping (RtSaved.slotVA p) = some n → ∀ i < 16, fin.mem[n + i]? = s.mem[n + i]?)
    (holds : Holds (upds k) s fin)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin :=
  LrField.ofOld (RtSaved.carry top n11 n354 frame (fun _ => holds) field.old) (link_carry top nBL holds field)

/-- Class (straight-line) steps: fin.mem = s.mem and Holds (upds k) s fin. -/
theorem carry_class {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252) (mem : fin.mem = s.mem) (holds : Holds (upds k) s fin)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin :=
  carry top n11 n354 nBL (fun _ _ n _ i _ => by rw [mem]) holds field

/-- Branch steps (incl. RETs): memory unchanged and GPRs kept. -/
theorem carry_branch {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252) (mem : fin.mem = s.mem) (gpr : fin.regs.gpr = s.regs.gpr)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin := by
  refine LrField.ofOld (RtSaved.carry_branch top n11 n354 mem gpr field.old) (fun r hr => ?_)
  obtain ⟨same, _⟩ := link_keep k top nBL.1 nBL.2.1 nBL.2.2 (by rw [hr]; rfl)
  rw [gpr]
  exact field.link r (same ▸ hr)

/-- Memory steps: WritesOnly `written` ⊆ D off the slot, Holds (upds k). -/
theorem carry_mem {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252)
    (written D : Nat → Prop) (wo : WritesOnly written (fun y => s.mem[y]?) (fun y => fin.mem[y]?))
    (inD : ∀ y, written y → D y)
    (off : 11 < k → k < 354 → ∀ y, D y → ∀ n, mapping (RtSaved.slotVA p) = some n → ¬ (n ≤ y ∧ y < n + 16))
    (holds : Holds (upds k) s fin)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin :=
  carry top n11 n354 nBL (fun lo hi n hn i hi' =>
    wo (n + i) (fun w => off lo hi (n + i) (inD _ w) n hn ⟨by omega, by omega⟩)) holds field

/-- Store step k = e.1 inside the slot phase, D := accPA e, from SlotSep. -/
theorem carry_store {s fin : NativeState} (sep : RtSaved.SlotSep p mapping)
    {e : Nat × Nat × Int × Nat × Bool} (he : e ∈ HeapV2Plan.symbolicAccesses) (hw : e.2.2.2.2 = true)
    (lo : 11 < e.1) (hi : e.1 < 354) (nBL : e.1 ≠ 15 ∧ e.1 ≠ 150 ∧ e.1 ≠ 252)
    (written : Nat → Prop) (wo : WritesOnly written (fun y => s.mem[y]?) (fun y => fin.mem[y]?))
    (inD : ∀ y, written y → RtSaved.accPA p mapping e y) (holds : Holds (upds e.1) s fin)
    (field : LrField p mapping base v19 v30 e.1 s) : LrField p mapping base v19 v30 (e.1 + 1) fin :=
  carry_mem (by omega) (by omega) (by omega) nBL written (RtSaved.accPA p mapping e) wo inD
    (fun _ _ => RtSaved.accPA_sep sep he hw lo hi) holds field

/-- BL steps (k = 15 / 150 / 252): memory unchanged; the BL writes the link X30 = PC + 4, which
starts the link (PC = base + offset k from ChainInv3). -/
theorem carry_bl {k : Nat} {s fin : NativeState} (hk : k = 15 ∨ k = 150 ∨ k = 252)
    (mem : fin.mem = s.mem) (lr : fin.regs.gpr[30] = s.regs._PC + 4#64)
    (pc : s.regs._PC = base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf k)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin := by
  have inside : 11 < k ∧ k < 354 := by omega
  refine LrField.ofOld (RtSaved.carry_slot inside.1 inside.2 (fun n _ i _ => by rw [mem]) field.old)
    (fun r hr => ?_)
  rw [lr, pc, BitVec.add_assoc]
  rcases hk with rfl | rfl | rfl
  · obtain rfl : r = 0x40 := by simp [linkRet] at hr <;> omega
    have e : ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf 15 + 4#64 = BitVec.ofNat 64 (0x10278 + 0x40) := by
      decide +kernel
    rw [e]
  · obtain rfl : r = 0x50 := by simp [linkRet] at hr <;> omega
    have e : ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf 150 + 4#64 = BitVec.ofNat 64 (0x10278 + 0x50) := by
      decide +kernel
    rw [e]
  · obtain rfl : r = 0x5c := by simp [linkRet] at hr <;> omega
    have e : ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf 252 + 4#64 = BitVec.ofNat 64 (0x10278 + 0x5c) := by
      decide +kernel
    rw [e]

/-- k = 11 (prologue STP): its payload; the link is vacuous at 12. -/
theorem carry_stp11 {s fin : NativeState}
    (payload : ∀ n, mapping (RtSaved.slotVA p) = some n → ∀ i < 16,
      fin.mem[n + i]? = some (RtSaved.slotByte (s.regs.gpr[19]) (s.regs.gpr[30]) i))
    (field : LrField p mapping base v19 v30 11 s) : LrField p mapping base v19 v30 12 fin :=
  LrField.ofOld (RtSaved.carry_stp11 payload field.old) (fun r h => by rw [link_none_12] at h; cases h)

/-- k = 354 (epilogue LDP): its payload; the link is vacuous at 355. -/
theorem carry_ldp354 {s fin : NativeState} (mapped : ∃ n, mapping (RtSaved.slotVA p) = some n)
    (payload : ∀ n, mapping (RtSaved.slotVA p) = some n → ∀ d : BitVec 128,
      (∀ i < 16, s.mem[n + i]? = some (d.extractLsb' (8 * i) 8)) →
      fin.regs.gpr[30] = ArmCertMem.LdpEval.ldpHi d)
    (field : LrField p mapping base v19 v30 354 s) : LrField p mapping base v19 v30 355 fin :=
  LrField.ofOld (RtSaved.carry_ldp354 mapped payload field.old) (fun r h => by rw [link_none_355] at h; cases h)

theorem field_stp11 {s fin : NativeState} (pay : RtSaved.MemFacts.StpPay p mapping RtSaved.slotEntry 19#5 30#5 s fin)
    (field : LrField p mapping base v19 v30 11 s) : LrField p mapping base v19 v30 12 fin :=
  LrField.ofOld (RtSaved.MemFacts.field_stp11 pay field.old) (fun r h => by rw [link_none_12] at h; cases h)

theorem field_ldp354 {s fin : NativeState} (mapped : ∃ n, mapping (RtSaved.slotVA p) = some n)
    (pay : RtSaved.MemFacts.LdpPay p mapping (354, 0, -16, 16, false) 30#5 s fin)
    (field : LrField p mapping base v19 v30 354 s) : LrField p mapping base v19 v30 355 fin :=
  LrField.ofOld (RtSaved.MemFacts.field_ldp354 mapped pay field.old) (fun r h => by rw [link_none_355] at h; cases h)

#print axioms link_keep
#print axioms field_zero
#print axioms lrSaved_of_chain
#print axioms link_target
#print axioms carry
#print axioms carry_class
#print axioms carry_branch
#print axioms carry_mem
#print axioms carry_store
#print axioms carry_bl
#print axioms carry_stp11
#print axioms carry_ldp354
#print axioms field_stp11
#print axioms field_ldp354
end RtSaved2
