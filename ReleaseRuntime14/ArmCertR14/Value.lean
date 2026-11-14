-- Memory (runtime14 memory classes): generic ArmCert-only value facts for single/pair loads and stores, over any
-- mapping / pinv / regions (runtime14's regions come from accesses_cNN). No Bridge / MemM1 / CruxMem imports.
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.Flags
import ArmCertValue.Core
import ArmCertValueMem.Region
set_option autoImplicit false
namespace ArmCertR14.Value
open ArmCertValue ArmCertValue.MemRegion
open HeapV2StepCerts.RegBind (Reg St regVal Upd updOf Holds)

/-- One GPR written (clobbered for the plan), SP unchanged. (Restated from HeapV2StepCerts.RegBind.holds_drop1.) -/
theorem holds_drop1 (x y : St) (R : Fin 31) (v : BitVec 64)
    (gpr : y.regs.gpr = x.regs.gpr.set R.val v R.isLt) (sp : y.regs.SP_EL0 = x.regs.SP_EL0) :
    Holds [(.x R, .drop)] x y := by
  intro r
  cases r with
  | sp => simp [updOf, List.find?, regVal, sp]
  | x j =>
    by_cases h : R = j
    · subst h; simp [updOf, List.find?]
    · have e : (Reg.x R = Reg.x j) = False := by simp [h]
      simp only [updOf, List.find?, e, decide_false, Option.map_none, Option.getD_none]
      simp only [regVal, gpr, Vector.getElem_set, Fin.val_inj]
      simp [h]

/-- extractLsb' of a word is its byteOf. -/
theorem extract_byteOf (d : BitVec 64) (k : Nat) : d.extractLsb' (8 * k) 8 = byteOf d k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteOf_getLsbD _ _ _ hi]
  simp [hi]

/-- Region bytes of word w from a linear mapping of its 8 VAs onto pa.. and the bytes there. -/
theorem regionBytes_of_lin (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St) (r : Region) (w pa : Nat)
    (d : BitVec 64)
    (lin : ∀ k : Nat, k < 8 → mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int))) = some (pa + k))
    (bytes : ∀ k, k < 8 → s.mem[pa + k]? = some (d.extractLsb' (8 * k) 8)) :
    ∀ k, k < 8 → regionByte mapping pinv s r (8 * w + k) = some (byteOf d k) := by
  intro k hk
  rw [regionByte_at, lin k hk, Option.bind_some, bytes k hk, extract_byteOf]

/-- Frames: with memory unchanged, every region word and byte reads the same. -/
theorem frames_of_mem (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (x y : St) (h : y.mem = x.mem)
    (r : Region) : (∀ w, regionWord mapping pinv y r w = regionWord mapping pinv x r w) ∧
      (∀ j, regionByte mapping pinv y r j = regionByte mapping pinv x r j) :=
  ⟨fun w => regionWord_congr mapping pinv x y r w (fun k _ => by simp only [regionByte, h]),
   fun j => by simp only [regionByte, h]⟩

/-- MemVHolds of loads (memory unchanged): each listed load's word is the destination's new value. -/
theorem memV_loads (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (x y : St)
    (effs : List MemEff) (h : y.mem = x.mem)
    (hl : ∀ e ∈ effs, ∃ rt r i, e = .load rt r i ∧ regionWord mapping pinv x r i = some (regVal y rt)) :
    MemVHolds mapping pinv regions effs x y := by
  refine ⟨fun e he => ?_, fun r _ w _ _ _ _ => (frames_of_mem mapping pinv x y h r).1 w,
    fun r _ j _ _ _ _ => (frames_of_mem mapping pinv x y h r).2 j⟩
  obtain ⟨rt, r, i, rfl, hv⟩ := hl e he
  exact hv

/-- A region word from its 8 bytes. -/
theorem regionWord_of_bytes (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St) (r : Region) (w : Nat)
    (d : BitVec 64) (hb : ∀ k, k < 8 → regionByte mapping pinv s r (8 * w + k) = some (byteOf d k)) :
    regionWord mapping pinv s r w = some d :=
  (regionWord_bytes mapping pinv s r w d).2 hb

/-- MemVHolds from unchanged memory and each effect's own clause (stated as MemVHolds over no regions). -/
theorem memV_of_mem (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (x y : St)
    (effs : List MemEff) (h : y.mem = x.mem) (hl : ∀ e ∈ effs, MemVHolds mapping pinv [] [e] x y) :
    MemVHolds mapping pinv regions effs x y :=
  ⟨fun e he => (hl e he).1 e (List.mem_singleton_self e),
   fun r _ w _ _ _ _ => (frames_of_mem mapping pinv x y h r).1 w,
   fun r _ j _ _ _ _ => (frames_of_mem mapping pinv x y h r).2 j⟩

/-- Byte (r, j) is untouched by effs in MemVHolds' byte-frame sense. -/
def ByteFree (effs : List MemEff) (r : Region) (j : Nat) : Prop :=
  (∀ rt, MemEff.storeb rt r j ∉ effs) ∧ (∀ rt, MemEff.store rt r (j / 8) ∉ effs) ∧
    (∀ rt j', MemEff.store32 rt r j' ∈ effs → ¬ (j' ≤ j ∧ j < j' + 4))

/-- MemVHolds from a write window [pa, pa + n) that misses every ByteFree tracked byte's PA, plus each effect's own
clause (stated as MemVHolds over no regions). -/
theorem memV_of_writes (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (x y : St)
    (effs : List MemEff) (pa n : Nat) (wo : ∀ q, ¬ (pa ≤ q ∧ q < pa + n) → y.mem[q]? = x.mem[q]?)
    (miss : ∀ r ∈ regions, ∀ j, j < 8 * r.words → ByteFree effs r j → ∀ q,
      mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + j)) = some q → ¬ (pa ≤ q ∧ q < pa + n))
    (hl : ∀ e ∈ effs, MemVHolds mapping pinv [] [e] x y) :
    MemVHolds mapping pinv regions effs x y := by
  have byte : ∀ r ∈ regions, ∀ j, j < 8 * r.words → ByteFree effs r j →
      regionByte mapping pinv y r j = regionByte mapping pinv x r j := by
    intro r hr j hj hf
    simp only [regionByte]
    cases hm : mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + j)) with
    | none => rfl
    | some q => exact wo q (miss r hr j hj hf q hm)
  refine ⟨fun e he => (hl e he).1 e (List.mem_singleton_self e), ?_, ?_⟩
  · intro r hr w hw h1 h2 h3
    refine regionWord_congr mapping pinv x y r w (fun k hk => byte r hr (8 * w + k) (by omega) ⟨?_, ?_, ?_⟩)
    · intro rt he; exact h2 rt _ he (by omega)
    · intro rt he; rw [show (8 * w + k) / 8 = w by omega] at he; exact h1 rt he
    · intro rt j' he; rcases h3 rt j' he with h | h <;> omega
  · intro r hr j hj h1 h2 h3
    exact byte r hr j hj ⟨h1, h2, h3⟩

/-- SP := SP + c, GPRs unchanged (STP pre-index). -/
theorem holds_sp (x y : St) (c : Int) (gpr : y.regs.gpr = x.regs.gpr)
    (sp : y.regs.SP_EL0 = x.regs.SP_EL0 + BitVec.ofInt 64 c) : Holds [(.sp, .set .sp c)] x y := by
  intro r
  cases r with
  | sp => simp [updOf, List.find?, regVal, sp]
  | x j => simp [updOf, List.find?, regVal, gpr]

/-- Two GPRs clobbered, then SP := SP + c (LDP post-index). -/
theorem holds_pair_sp (x y : St) (R R2 : Fin 31) (c : Int) (v v2 : BitVec 64)
    (gpr : y.regs.gpr = (x.regs.gpr.set R.val v R.isLt).set R2.val v2 R2.isLt)
    (sp : y.regs.SP_EL0 = x.regs.SP_EL0 + BitVec.ofInt 64 c) :
    Holds [(.x R, .drop), (.x R2, .drop), (.sp, .set .sp c)] x y := by
  intro r
  cases r with
  | sp => simp [updOf, List.find?, regVal, sp]
  | x j =>
    by_cases h1 : R = j
    · subst h1; simp [updOf, List.find?]
    by_cases h2 : R2 = j
    · subst h2; simp [updOf, List.find?, h1]
    have e1 : (Reg.x R = Reg.x j) = False := by simp [h1]
    have e2 : (Reg.x R2 = Reg.x j) = False := by simp [h2]
    simp only [updOf, List.find?, e1, e2, decide_false]
    simp only [regVal, gpr, Vector.getElem_set, Fin.val_inj]
    simp [h1, h2]

/-- MemVHolds of a 16-byte pair store at word w, w + 1 (bytes g at pa.., linear VAs, other tracked bytes miss). -/
theorem memV_storePair (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (x y : St)
    (rt rt2 : Reg) (r : Region) (w pa : Nat) (g : Nat → BitVec 8)
    (hin : ∀ k, k < 16 → y.mem[pa + k]? = some (g k))
    (wo : ∀ q, ¬ (pa ≤ q ∧ q < pa + 16) → y.mem[q]? = x.mem[q]?)
    (glo : ∀ k, k < 8 → g k = byteOf (regVal x rt) k) (ghi : ∀ k, k < 8 → g (8 + k) = byteOf (regVal x rt2) k)
    (lin : ∀ k : Nat, k < 16 → mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int))) = some (pa + k))
    (miss : ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words → ByteFree [.store rt r w, .store rt2 r (w + 1)] r' j' → ∀ q,
      mapping (BitVec.ofInt 64 ((pinv r'.pin : Int) + r'.off + j')) = some q → ¬ (pa ≤ q ∧ q < pa + 16)) :
    MemVHolds mapping pinv regions [.store rt r w, .store rt2 r (w + 1)] x y := by
  refine memV_of_writes mapping pinv regions x y _ pa 16 wo miss (fun e he => ?_)
  refine ⟨fun e' he' => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he'; subst he'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · refine regionWord_of_bytes mapping pinv y r w _ (fun k hk => ?_)
    rw [regionByte_at, lin k (by omega), Option.bind_some, hin k (by omega), glo k hk]
  · refine regionWord_of_bytes mapping pinv y r (w + 1) _ (fun k hk => ?_)
    rw [regionByte_at]
    have e : (pinv r.pin : Int) + r.off + 8 * ((w + 1 : Nat) : Int) + (k : Int) =
        (pinv r.pin : Int) + r.off + 8 * (w : Int) + ((8 + k : Nat) : Int) := by push_cast; omega
    rw [e, lin (8 + k) (by omega), Option.bind_some, hin (8 + k) (by omega), ghi k hk]

/-- MemVHolds of a 16-byte pair load into rt (word w) and rt2 (word w + 1), memory unchanged. -/
theorem memV_loadPair (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (x y : St)
    (rt rt2 : Reg) (r : Region) (w pa : Nat) (g : Nat → BitVec 8) (h : y.mem = x.mem)
    (hin : ∀ k, k < 16 → x.mem[pa + k]? = some (g k))
    (glo : ∀ k, k < 8 → g k = byteOf (regVal y rt) k) (ghi : ∀ k, k < 8 → g (8 + k) = byteOf (regVal y rt2) k)
    (lin : ∀ k : Nat, k < 16 → mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int))) = some (pa + k)) :
    MemVHolds mapping pinv regions [.load rt r w, .load rt2 r (w + 1)] x y := by
  refine memV_of_mem mapping pinv regions x y _ h (fun e he => ?_)
  refine ⟨fun e' he' => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he'; subst he'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · refine regionWord_of_bytes mapping pinv x r w _ (fun k hk => ?_)
    rw [regionByte_at, lin k (by omega), Option.bind_some, hin k (by omega), glo k hk]
  · refine regionWord_of_bytes mapping pinv x r (w + 1) _ (fun k hk => ?_)
    rw [regionByte_at]
    have e : (pinv r.pin : Int) + r.off + 8 * ((w + 1 : Nat) : Int) + (k : Int) =
        (pinv r.pin : Int) + r.off + 8 * (w : Int) + ((8 + k : Nat) : Int) := by push_cast; omega
    rw [e, lin (8 + k) (by omega), Option.bind_some, hin (8 + k) (by omega), ghi k hk]

#print axioms holds_sp
#print axioms holds_pair_sp
#print axioms memV_storePair
#print axioms memV_loadPair
#print axioms memV_of_writes
#print axioms memV_of_mem
#print axioms holds_drop1
#print axioms regionBytes_of_lin
#print axioms memV_loads
#print axioms regionWord_of_bytes
end ArmCertR14.Value
