-- (H-P4 + D180a (2), /): the shim DIT window and restoration, generic.
-- Indices (RtShim.ShimInv): s0..s6 = 0..6, body k = 0..357 at 7..364 (its final RET lands at 365),
-- s7..s10 = 365..368, caller at 369. Over σ j = stateAt real e j:
--   dit_window : the per-step facts (each the conclusion of an RtDit.Shim.shim_* lemma, or of body_slot)
--                give DIT (σ j) = 1 for 5 ≤ j ≤ 367 (through s9's input), DIT (σ 368) = DIT (σ 369) = DIT e.
--   body_slot  : over e17_general's deployment at the body entry σ 7, with the slot separated from the plan's
--                data bytes: DIT (σ j) = DIT (σ 7) and the shim slot is untouched, 7 ≤ j ≤ 365.
import RtDit2.ShimDit
import RtDit2.DitBodyM
import RtS3.Link3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace RtDit.Window
open RtDit RtDit.Shim

/-- The slot's 16 bytes are unchanged from s to f. -/
def SlotKeep (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (s f : NativeState) : Prop :=
  ∀ n, mapping (BitVec.ofNat 64 p.sp) = some n → ∀ i < 16, f.mem[n + i]? = s.mem[n + i]?

theorem enc_bit (d : BitVec 1) : (((0#39 +++ d) +++ 0#24).extractLsb 24 24) = d := by
  have h := d.isLt
  rcases (show d = 0#1 ∨ d = 1#1 by
    by_cases h0 : d.toNat = 0
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h0]))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simp; omega))) with rfl | rfl <;> decide

theorem ldpLo_stpData (s : NativeState) :
    ArmCertMem.LdpEval.ldpLo (ArmCertMem.StpEval.stpData s 9#5 30#5) = s.regs.gpr[9] := by
  unfold ArmCertMem.StpEval.stpData
  exact RtSaved3.ldpLo_append _ _

theorem stateAt_add (real : Type) [Sail.SailReal real] (s : NativeState) (a : Nat) :
    ∀ b, stateAt real s (a + b) = stateAt real (stateAt real s a) b
  | 0 => rfl
  | b + 1 => by
    show next real (stateAt real s (a + b)) = next real (stateAt real (stateAt real s a) b)
    rw [stateAt_add real s a b]

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Window.dit_window"
  (← IO.getStderr).flush

theorem dit_window (real : Type) [Sail.SailReal real] (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat)
    (e : NativeState)
    (h0 : ∃ fin, modelStep real (stateAt real e 0) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 0).regs.PSTATE.DIT)
    (h1 : ∃ fin, modelStep real (stateAt real e 1) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 1).regs.PSTATE.DIT)
    (h2 : ∃ fin, modelStep real (stateAt real e 2) = .ok () fin ∧
      fin.regs.gpr[9] = (0#39 +++ (stateAt real e 2).regs.PSTATE.DIT) +++ 0#24 ∧
      fin.regs.PSTATE.DIT = (stateAt real e 2).regs.PSTATE.DIT)
    (h3 : ∃ fin, modelStep real (stateAt real e 3) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 3).regs.PSTATE.DIT ∧
      SlotHas p mapping (ArmCertMem.StpEval.stpData (stateAt real e 3) 9#5 30#5) fin)
    (h4 : ∃ fin, modelStep real (stateAt real e 4) = .ok () fin ∧ fin.regs.PSTATE.DIT = 1#1 ∧
      fin.mem = (stateAt real e 4).mem)
    (h5 : ∃ fin, modelStep real (stateAt real e 5) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 5).regs.PSTATE.DIT ∧ fin.mem = (stateAt real e 5).mem)
    (h6 : ∃ fin, modelStep real (stateAt real e 6) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 6).regs.PSTATE.DIT ∧ MemFrame (fun _ => False) (stateAt real e 6) fin)
    (hbody : ∀ j, 7 ≤ j → j ≤ 365 → (stateAt real e j).regs.PSTATE.DIT = (stateAt real e 7).regs.PSTATE.DIT ∧
      SlotKeep p mapping (stateAt real e 7) (stateAt real e j))
    (h365 : ∃ fin, modelStep real (stateAt real e 365) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 365).regs.PSTATE.DIT ∧
      ∀ d : BitVec 128, SlotHas p mapping d (stateAt real e 365) → fin.regs.gpr[9] = ArmCertMem.LdpEval.ldpLo d)
    (h366 : ∃ fin, modelStep real (stateAt real e 366) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 366).regs.PSTATE.DIT ∧ fin.regs.gpr[9] = (stateAt real e 366).regs.gpr[9])
    (h367 : ∃ fin, modelStep real (stateAt real e 367) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 367).regs.gpr[9].extractLsb 24 24)
    (h368 : ∃ fin, modelStep real (stateAt real e 368) = .ok () fin ∧
      fin.regs.PSTATE.DIT = (stateAt real e 368).regs.PSTATE.DIT) :
    (∀ j, 5 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
      (stateAt real e 368).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧
      (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT := by
  obtain ⟨f, r, d1⟩ := h0
  have e1 : stateAt real e 1 = f := stateAt_succ_of r
  rw [← e1] at d1
  obtain ⟨f, r, d2⟩ := h1
  have e2 : stateAt real e 2 = f := stateAt_succ_of r
  rw [← e2] at d2
  obtain ⟨f, r, x3, d3⟩ := h2
  have e3 : stateAt real e 3 = f := stateAt_succ_of r
  rw [← e3] at x3 d3
  obtain ⟨f, r, d4, s4⟩ := h3
  have e4 : stateAt real e 4 = f := stateAt_succ_of r
  rw [← e4] at d4 s4
  obtain ⟨f, r, d5, m5⟩ := h4
  have e5 : stateAt real e 5 = f := stateAt_succ_of r
  rw [← e5] at d5 m5
  obtain ⟨f, r, d6, m6⟩ := h5
  have e6 : stateAt real e 6 = f := stateAt_succ_of r
  rw [← e6] at d6 m6
  obtain ⟨f, r, d7, m7⟩ := h6
  have e7 : stateAt real e 7 = f := stateAt_succ_of r
  rw [← e7] at d7 m7
  obtain ⟨f, r, d366, x366⟩ := h365
  have e366 : stateAt real e 366 = f := stateAt_succ_of r
  rw [← e366] at d366 x366
  obtain ⟨f, r, d367, x367⟩ := h366
  have e367 : stateAt real e 367 = f := stateAt_succ_of r
  rw [← e367] at d367 x367
  obtain ⟨f, r, d368⟩ := h367
  have e368 : stateAt real e 368 = f := stateAt_succ_of r
  rw [← e368] at d368
  obtain ⟨f, r, d369⟩ := h368
  have e369 : stateAt real e 369 = f := stateAt_succ_of r
  rw [← e369] at d369
  have D0 : (stateAt real e 2).regs.PSTATE.DIT = e.regs.PSTATE.DIT := d2.trans (d1.trans rfl)
  have one7 : (stateAt real e 7).regs.PSTATE.DIT = 1#1 := d7.trans (d6.trans d5)
  -- the slot from s3's store to s7's load
  have slot365 : SlotHas p mapping (ArmCertMem.StpEval.stpData (stateAt real e 3) 9#5 30#5) (stateAt real e 365) := by
    intro n hn i hi
    rw [(hbody 365 (by omega) (Nat.le_refl _)).2 n hn i hi, m7 (n + i) id, m6, m5]
    exact s4 n hn i hi
  have x9 : (stateAt real e 367).regs.gpr[9] = (0#39 +++ e.regs.PSTATE.DIT) +++ 0#24 := by
    rw [x367, x366 _ slot365, ldpLo_stpData, x3, D0]
  have one365 : (stateAt real e 365).regs.PSTATE.DIT = 1#1 := (hbody 365 (by omega) (Nat.le_refl _)).1.trans one7
  have r368 : (stateAt real e 368).regs.PSTATE.DIT = e.regs.PSTATE.DIT := by
    rw [d368, x9, enc_bit]
  refine ⟨fun j lo hi => ?_, r368, d369.trans r368⟩
  rcases (show j = 5 ∨ j = 6 ∨ (7 ≤ j ∧ j ≤ 365) ∨ j = 366 ∨ j = 367 by omega) with
    rfl | rfl | ⟨a, b⟩ | rfl | rfl
  · exact d5
  · exact d6.trans d5
  · exact (hbody j a b).1.trans one7
  · exact d366.trans one365
  · exact d367.trans (d366.trans one365)

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Window.body_slot"
  (← IO.getStderr).flush

/-- The body (states 7..365 of the shim run, incl. its final RET) keeps DIT and the shim slot, given
e17_general's deployment at the body entry σ 7 and the slot separated from the plan's data bytes. -/
theorem body_slot (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (p : HeapV2E17.Pins) (e : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base p (stateAt real e 7) budget) (hb : 358 ≤ budget)
    (hlow : ((stateAt real (stateAt real e 7) 357).regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55)
    (sep : ∀ a, RtShim2.ShimMem.slotBytes p mapping a → ¬ HeapV2StepCerts.MemNext.dataBytes p mapping a) :
    ∀ j, 7 ≤ j → j ≤ 365 → (stateAt real e j).regs.PSTATE.DIT = (stateAt real e 7).regs.PSTATE.DIT ∧
      SlotKeep p mapping (stateAt real e 7) (stateAt real e j) := by
  intro j lo hi
  obtain ⟨k, rfl⟩ : ∃ k, j = 7 + k := ⟨j - 7, by omega⟩
  rw [stateAt_add real e 7 k]
  have fr : (stateAt real (stateAt real e 7) k).regs.PSTATE.DIT = (stateAt real e 7).regs.PSTATE.DIT ∧
      MemFrame (HeapV2StepCerts.MemNext.dataBytes p mapping) (stateAt real e 7) (stateAt real (stateAt real e 7) k) := by
    rcases Nat.lt_or_ge k 358 with h | h
    · exact dit_body_mem real spec config rows mapping base p (stateAt real e 7) budget dp (by omega) k (by omega)
    · obtain rfl : k = 358 := by omega
      exact dit_body_ret real spec config rows mapping base p (stateAt real e 7) budget dp hb hlow
  refine ⟨fr.1, fun n hn i hi => fr.2 (n + i) (sep _ ⟨n, hn, by omega, by omega⟩)⟩

#print axioms enc_bit
#print axioms ldpLo_stpData
#print axioms stateAt_add
#print axioms dit_window
#print axioms body_slot
end RtDit.Window
