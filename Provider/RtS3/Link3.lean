-- rich-v6 (B1 (a)): LrField v3 = RtSaved2.LrField + high19 (X19 = entry from the
-- epilogue LDP on), so X19 at k = 357 equals entry X19. The LDP at 354 restores X19 := ldpLo of the slot;
-- 355/356 keep X19 (upds table). All other carries are LRSaved2's (forgetful map) plus the X19 keep.
import RtS2.Link
import RtS3.MemFacts2
open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft (NativeState)
open HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 4096
set_option Elab.async false
namespace RtSaved3

structure LrField (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (v19 v30 : BitVec 64) (k : Nat) (x : NativeState) : Prop where
  low : k ≤ 11 → x.regs.gpr[19] = v19 ∧ x.regs.gpr[30] = v30
  slot : 11 < k → k ≤ 354 → RtSaved.SlotHolds p mapping v19 v30 x
  high : 354 < k → x.regs.gpr[30] = v30
  link : ∀ r, RtSaved2.linkRet k = some r → x.regs.gpr[30] = base + BitVec.ofNat 64 (0x10278 + r)
  high19 : 354 < k → x.regs.gpr[19] = v19

variable {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {base v19 v30 : BitVec 64}

theorem LrField.old {k : Nat} {x : NativeState} (f : LrField p mapping base v19 v30 k x) :
    RtSaved2.LrField p mapping base v19 v30 k x := ⟨f.low, f.slot, f.high, f.link⟩

theorem LrField.ofOld {k : Nat} {x : NativeState} (f : RtSaved2.LrField p mapping base v19 v30 k x)
    (h19 : 354 < k → x.regs.gpr[19] = v19) : LrField p mapping base v19 v30 k x :=
  ⟨f.low, f.slot, f.high, f.link, h19⟩

theorem keep19_high' : ∀ j, j < 3 → updOf (upds (355 + j)) (.x 19) = .keep := by decide

theorem keep19_high : ∀ k, 355 ≤ k → k < 358 → updOf (upds k) (.x 19) = .keep := by
  intro k lo hi
  have h := keep19_high' (k - 355) (by omega)
  rwa [show 355 + (k - 355) = k by omega] at h

theorem high19_carry {k : Nat} {s fin : NativeState} (top : k < 358) (n354 : k ≠ 354)
    (holds : Holds (upds k) s fin) (field : LrField p mapping base v19 v30 k s) :
    354 < k + 1 → fin.regs.gpr[19] = v19 := by
  intro h
  have k19 : fin.regs.gpr[19] = s.regs.gpr[19] := RtSaved.kept_reg holds 19 (keep19_high k (by omega) top)
  rw [k19]; exact field.high19 (by omega)

theorem field_zero (entry : NativeState) :
    LrField p mapping base (entry.regs.gpr[19]) (entry.regs.gpr[30]) 0 entry :=
  LrField.ofOld (RtSaved2.field_zero entry) (fun h => absurd h (by decide))

theorem lrSaved_of_chain {x : NativeState} (field : LrField p mapping base v19 v30 357 x) :
    x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = v30 :=
  RtSaved2.lrSaved_of_chain field.old

/-- X19 at the RET (k = 357) is its entry value (the slot round trip + LDP low half). -/
theorem x19_of_chain {x : NativeState} (field : LrField p mapping base v19 v30 357 x) :
    x.regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = v19 := by
  simp only [show (GPRSummary.key (19#5 : BitVec 5).toNat).val = 19 by decide]
  exact field.high19 (by decide)

theorem link_target {k : Nat} {x : NativeState} (hk : k = 146 ∨ k = 249 ∨ k = 331)
    (field : LrField p mapping base v19 v30 k x) :
    x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] =
      base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (k + 1) :=
  RtSaved2.link_target hk field.old

theorem carry {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252)
    (frame : 11 < k → k < 354 → ∀ n, mapping (RtSaved.slotVA p) = some n → ∀ i < 16, fin.mem[n + i]? = s.mem[n + i]?)
    (holds : Holds (upds k) s fin)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin :=
  LrField.ofOld (RtSaved2.carry top n11 n354 nBL frame holds field.old) (high19_carry top n354 holds field)

theorem carry_class {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252) (mem : fin.mem = s.mem) (holds : Holds (upds k) s fin)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin :=
  LrField.ofOld (RtSaved2.carry_class top n11 n354 nBL mem holds field.old) (high19_carry top n354 holds field)

theorem carry_branch {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252) (mem : fin.mem = s.mem) (gpr : fin.regs.gpr = s.regs.gpr)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin :=
  LrField.ofOld (RtSaved2.carry_branch top n11 n354 nBL mem gpr field.old)
    (fun h => by rw [gpr]; exact field.high19 (by omega))

theorem carry_mem {k : Nat} {s fin : NativeState} (top : k < 358) (n11 : k ≠ 11) (n354 : k ≠ 354)
    (nBL : k ≠ 15 ∧ k ≠ 150 ∧ k ≠ 252)
    (written D : Nat → Prop) (wo : WritesOnly written (fun y => s.mem[y]?) (fun y => fin.mem[y]?))
    (inD : ∀ y, written y → D y)
    (off : 11 < k → k < 354 → ∀ y, D y → ∀ n, mapping (RtSaved.slotVA p) = some n → ¬ (n ≤ y ∧ y < n + 16))
    (holds : Holds (upds k) s fin)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin :=
  LrField.ofOld (RtSaved2.carry_mem top n11 n354 nBL written D wo inD off holds field.old)
    (high19_carry top n354 holds field)

theorem carry_store {s fin : NativeState} (sep : RtSaved.SlotSep p mapping)
    {e : Nat × Nat × Int × Nat × Bool} (he : e ∈ HeapV2Plan.symbolicAccesses) (hw : e.2.2.2.2 = true)
    (lo : 11 < e.1) (hi : e.1 < 354) (nBL : e.1 ≠ 15 ∧ e.1 ≠ 150 ∧ e.1 ≠ 252)
    (written : Nat → Prop) (wo : WritesOnly written (fun y => s.mem[y]?) (fun y => fin.mem[y]?))
    (inD : ∀ y, written y → RtSaved.accPA p mapping e y) (holds : Holds (upds e.1) s fin)
    (field : LrField p mapping base v19 v30 e.1 s) : LrField p mapping base v19 v30 (e.1 + 1) fin :=
  LrField.ofOld (RtSaved2.carry_store sep he hw lo hi nBL written wo inD holds field.old)
    (fun h => absurd h (by omega))

theorem carry_bl {k : Nat} {s fin : NativeState} (hk : k = 15 ∨ k = 150 ∨ k = 252)
    (mem : fin.mem = s.mem) (lr : fin.regs.gpr[30] = s.regs._PC + 4#64)
    (pc : s.regs._PC = base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf k)
    (field : LrField p mapping base v19 v30 k s) : LrField p mapping base v19 v30 (k + 1) fin :=
  LrField.ofOld (RtSaved2.carry_bl hk mem lr pc field.old) (fun h => absurd h (by omega))

theorem field_stp11 {s fin : NativeState} (pay : RtSaved.MemFacts.StpPay p mapping RtSaved.slotEntry 19#5 30#5 s fin)
    (field : LrField p mapping base v19 v30 11 s) : LrField p mapping base v19 v30 12 fin :=
  LrField.ofOld (RtSaved2.field_stp11 pay field.old) (fun h => absurd h (by decide))

theorem ldpLo_append (hi lo : BitVec 64) :
    ArmCertMem.LdpEval.ldpLo (BitVec.cast (by decide : 64 + 64 = 128) (BitVec.append hi lo)) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [ArmCertMem.LdpEval.ldpLo, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, Sail.BitVec.castWidth,
    dite_true, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast]
  rw [BitVec.append_eq, BitVec.getLsbD_append]
  simp [hi']

/-- k = 354 (LDP x19, x30, [sp, #48]) with both halves: X30 and X19 back to their entry values. -/
theorem field_ldp354 {s fin : NativeState} (mapped : ∃ n, mapping (RtSaved.slotVA p) = some n)
    (pay : RtSaved3.MemFacts2.LdpPay2 p mapping (354, 0, -16, 16, false) 19#5 30#5 s fin)
    (field : LrField p mapping base v19 v30 354 s) : LrField p mapping base v19 v30 355 fin := by
  refine LrField.ofOld (RtSaved2.field_ldp354 mapped pay.toPay field.old) (fun _ => ?_)
  obtain ⟨n, hn⟩ := mapped
  have h := (pay n hn (BitVec.cast (by decide) (BitVec.append v30 v19)) (fun i hi => by
    rw [field.slot (by decide) (by decide) n hn i hi]; rfl)).2
  simp only [show (rk (19#5)).val = 19 by decide] at h
  rw [h]; exact ldpLo_append v30 v19

#print axioms keep19_high
#print axioms field_zero
#print axioms x19_of_chain
#print axioms carry
#print axioms carry_class
#print axioms carry_branch
#print axioms carry_mem
#print axioms carry_store
#print axioms carry_bl
#print axioms field_stp11
#print axioms ldpLo_append
#print axioms field_ldp354
end RtSaved3
