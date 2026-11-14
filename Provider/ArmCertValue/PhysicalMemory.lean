-- Memory (runtime14 memory classes): generic ArmCert-only value facts for single/pair loads and stores, over any
-- mapping / pinv / regions (runtime14's regions come from accesses_cNN). No Bridge / MemM1 / CruxMem imports.
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.Flags
import ArmCertValue.PhysicalLemmas
import ArmCertValueMem.Region
set_option autoImplicit false
namespace ArmCertValue.Physical
open ArmCertValue.MemRegion (byteOf byteOf_getLsbD)
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

/-- Region bytes of word w from a physical-byte view onto pa.. and the bytes there. -/
theorem regionBytes_of_span (bytePA : BytePA) (s : St) (r : Region) (w pa : Nat)
    (d : BitVec 64)
    (lin : ∀ k : Nat, k < 8 → bytePA r (8 * w + k) = some (pa + k))
    (bytes : ∀ k, k < 8 → s.mem[pa + k]? = some (d.extractLsb' (8 * k) 8)) :
    ∀ k, k < 8 → regionByte bytePA s r (8 * w + k) = some (byteOf d k) := by
  intro k hk
  rw [regionByte, lin k hk, Option.bind_some, bytes k hk, extract_byteOf]

/-- Frames: with memory unchanged, every region word and byte reads the same. -/
theorem frames_of_mem (bytePA : BytePA) (x y : St) (h : y.mem = x.mem)
    (r : Region) : (∀ w, regionWord bytePA y r w = regionWord bytePA x r w) ∧
      (∀ j, regionByte bytePA y r j = regionByte bytePA x r j) :=
  ⟨fun w => regionWord_congr bytePA x y r w (fun k _ => by simp only [regionByte, h]),
   fun j => by simp only [regionByte, h]⟩

/-- MemVHolds of loads (memory unchanged): each listed load's word is the destination's new value. -/
theorem memV_loads (bytePA : BytePA) (regions : List Region) (x y : St)
    (effs : List MemEff) (h : y.mem = x.mem)
    (hl : ∀ e ∈ effs, ∃ rt r i, e = .load rt r i ∧ regionWord bytePA x r i = some (regVal y rt)) :
    MemVHolds bytePA regions effs x y := by
  refine ⟨fun e he => ?_, fun r _ w _ _ _ _ => (frames_of_mem bytePA x y h r).1 w,
    fun r _ j _ _ _ _ => (frames_of_mem bytePA x y h r).2 j⟩
  obtain ⟨rt, r, i, rfl, hv⟩ := hl e he
  exact hv

/-- A region word from its 8 bytes. -/
theorem regionWord_of_bytes (bytePA : BytePA) (s : St) (r : Region) (w : Nat)
    (d : BitVec 64) (hb : ∀ k, k < 8 → regionByte bytePA s r (8 * w + k) = some (byteOf d k)) :
    regionWord bytePA s r w = some d :=
  (regionWord_bytes bytePA s r w d).2 hb

/-- MemVHolds from unchanged memory and each effect's own clause (stated as MemVHolds over no regions). -/
theorem memV_of_mem (bytePA : BytePA) (regions : List Region) (x y : St)
    (effs : List MemEff) (h : y.mem = x.mem) (hl : ∀ e ∈ effs, MemVHolds bytePA [] [e] x y) :
    MemVHolds bytePA regions effs x y :=
  ⟨fun e he => (hl e he).1 e (List.mem_singleton_self e),
   fun r _ w _ _ _ _ => (frames_of_mem bytePA x y h r).1 w,
   fun r _ j _ _ _ _ => (frames_of_mem bytePA x y h r).2 j⟩

/-- Byte (r, j) is untouched by effs in MemVHolds' byte-frame sense. -/
def ByteFree (effs : List MemEff) (r : Region) (j : Nat) : Prop :=
  (∀ rt, MemEff.storeb rt r j ∉ effs) ∧ (∀ rt, MemEff.store rt r (j / 8) ∉ effs) ∧
    (∀ rt j', MemEff.store32 rt r j' ∈ effs → ¬ (j' ≤ j ∧ j < j' + 4))

/-- MemVHolds from a write window [pa, pa + n) that misses every ByteFree tracked byte's PA, plus each effect's own
clause (stated as MemVHolds over no regions). -/
theorem memV_of_writes (bytePA : BytePA) (regions : List Region) (x y : St)
    (effs : List MemEff) (pa n : Nat) (wo : ∀ q, ¬ (pa ≤ q ∧ q < pa + n) → y.mem[q]? = x.mem[q]?)
    (miss : ∀ r ∈ regions, ∀ j, j < 8 * r.words → ByteFree effs r j → ∀ q,
      bytePA r j = some q → ¬ (pa ≤ q ∧ q < pa + n))
    (hl : ∀ e ∈ effs, MemVHolds bytePA [] [e] x y) :
    MemVHolds bytePA regions effs x y := by
  have byte : ∀ r ∈ regions, ∀ j, j < 8 * r.words → ByteFree effs r j →
      regionByte bytePA y r j = regionByte bytePA x r j := by
    intro r hr j hj hf
    simp only [regionByte]
    cases hm : bytePA r j with
    | none => rfl
    | some q => exact wo q (miss r hr j hj hf q hm)
  refine ⟨fun e he => (hl e he).1 e (List.mem_singleton_self e), ?_, ?_⟩
  · intro r hr w hw h1 h2 h3
    refine regionWord_congr bytePA x y r w (fun k hk => byte r hr (8 * w + k) (by omega) ⟨?_, ?_, ?_⟩)
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

/-- MemVHolds of a 16-byte pair store at word w, w + 1 (bytes g at pa.., physical-byte view, other tracked bytes miss). -/
theorem memV_storePair (bytePA : BytePA) (regions : List Region) (x y : St)
    (rt rt2 : Reg) (r : Region) (w pa : Nat) (g : Nat → BitVec 8)
    (hin : ∀ k, k < 16 → y.mem[pa + k]? = some (g k))
    (wo : ∀ q, ¬ (pa ≤ q ∧ q < pa + 16) → y.mem[q]? = x.mem[q]?)
    (glo : ∀ k, k < 8 → g k = byteOf (regVal x rt) k) (ghi : ∀ k, k < 8 → g (8 + k) = byteOf (regVal x rt2) k)
    (lin : ∀ k : Nat, k < 16 → bytePA r (8 * w + k) = some (pa + k))
    (miss : ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words → ByteFree [.store rt r w, .store rt2 r (w + 1)] r' j' → ∀ q,
      bytePA r' j' = some q → ¬ (pa ≤ q ∧ q < pa + 16)) :
    MemVHolds bytePA regions [.store rt r w, .store rt2 r (w + 1)] x y := by
  refine memV_of_writes bytePA regions x y _ pa 16 wo miss (fun e he => ?_)
  refine ⟨fun e' he' => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he'; subst he'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · refine regionWord_of_bytes bytePA y r w _ (fun k hk => ?_)
    rw [regionByte, lin k (by omega), Option.bind_some, hin k (by omega), glo k hk]
  · refine regionWord_of_bytes bytePA y r (w + 1) _ (fun k hk => ?_)
    rw [show 8 * (w + 1) + k = 8 * w + (8 + k) by omega, regionByte, lin (8 + k) (by omega), Option.bind_some, hin (8 + k) (by omega), ghi k hk]

/-- MemVHolds of a 16-byte pair load into rt (word w) and rt2 (word w + 1), memory unchanged. -/
theorem memV_loadPair (bytePA : BytePA) (regions : List Region) (x y : St)
    (rt rt2 : Reg) (r : Region) (w pa : Nat) (g : Nat → BitVec 8) (h : y.mem = x.mem)
    (hin : ∀ k, k < 16 → x.mem[pa + k]? = some (g k))
    (glo : ∀ k, k < 8 → g k = byteOf (regVal y rt) k) (ghi : ∀ k, k < 8 → g (8 + k) = byteOf (regVal y rt2) k)
    (lin : ∀ k : Nat, k < 16 → bytePA r (8 * w + k) = some (pa + k)) :
    MemVHolds bytePA regions [.load rt r w, .load rt2 r (w + 1)] x y := by
  refine memV_of_mem bytePA regions x y _ h (fun e he => ?_)
  refine ⟨fun e' he' => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he'; subst he'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · refine regionWord_of_bytes bytePA x r w _ (fun k hk => ?_)
    rw [regionByte, lin k (by omega), Option.bind_some, hin k (by omega), glo k hk]
  · refine regionWord_of_bytes bytePA x r (w + 1) _ (fun k hk => ?_)
    rw [show 8 * (w + 1) + k = 8 * w + (8 + k) by omega, regionByte, lin (8 + k) (by omega), Option.bind_some, hin (8 + k) (by omega), ghi k hk]


/-- All byte locations covered by a list of regions. -/
def trackedBytes (regions : List Region) : List (Region × Nat) :=
  regions.flatMap fun r => (List.range (8 * r.words)).map fun j => (r, j)

def RegionsInjective (bytePA : BytePA) (regions : List Region) : Prop :=
  ∀ a ∈ trackedBytes regions, ∀ b ∈ trackedBytes regions, a ≠ b → ∀ pa,
    bytePA a.1 a.2 = some pa → bytePA b.1 b.2 ≠ some pa

theorem frame_of_cover (bytePA : BytePA) (regions : List Region) (x y : St)
    (written : Nat → Prop) (wo : ∀ pa, ¬ written pa → y.mem[pa]? = x.mem[pa]?)
    (stored : List (Region × Nat))
    (cover : ∀ pa, written pa → ∃ b ∈ stored, bytePA b.1 b.2 = some pa)
    (inj : RegionsInjective bytePA regions)
    (hst : ∀ b ∈ stored, b ∈ trackedBytes regions)
    (r : Region) (j : Nat) (hrj : (r, j) ∈ trackedBytes regions) (hns : (r, j) ∉ stored) :
    regionByte bytePA y r j = regionByte bytePA x r j := by
  unfold regionByte
  cases h : bytePA r j with
  | none => rfl
  | some pa =>
    simp only [Option.bind_some]
    apply wo pa
    intro hw
    obtain ⟨b, hb, hbm⟩ := cover pa hw
    exact inj (r, j) hrj b (hst b hb) (fun e => hns (e ▸ hb)) pa h hbm

theorem present_of_agrees {bytePA : BytePA} {vals : List (BitVec 64)} {σ : Sym} {x : St}
    (h : Agrees bytePA vals σ x) {r : Region} {j i k : Nat}
    (hb : σ.memB r j = some (i, k)) {pa : Nat} (hq : bytePA r j = some pa) :
    (x.mem[pa]?).isSome := by
  have e := h.2.2 r j i k hb
  unfold regionByte at e
  rw [hq, Option.bind_some] at e
  rw [e]; rfl

/-- Agrees provides the individual physical bytes of an actual Sail access. -/
theorem bytes_present_of_agrees {bytePA : BytePA} {vals : List (BitVec 64)} {σ : Sym} {x : St}
    (h : Agrees bytePA vals σ x) (r : Region) (j0 n pa : Nat)
    (span : ∀ t, t < n → bytePA r (j0 + t) = some (pa + t))
    (cov : ∀ t, t < n → ∃ i k, σ.memB r (j0 + t) = some (i, k)) :
    ∀ t, t < n → (x.mem[pa + t]?).isSome := by
  intro t ht
  obtain ⟨i, k, hb⟩ := cov t ht
  exact present_of_agrees h hb (span t ht)

/-- The memory-free step case. -/
theorem memV_nil_of_mem (bytePA : BytePA) (regions : List Region) (x y : St) (h : y.mem = x.mem) :
    MemVHolds bytePA regions [] x y :=
  memV_of_mem bytePA regions x y [] h (fun e he => by cases he)

#print axioms frame_of_cover
#print axioms present_of_agrees
#print axioms bytes_present_of_agrees
#print axioms memV_nil_of_mem

#print axioms holds_sp
#print axioms holds_pair_sp
#print axioms memV_storePair
#print axioms memV_loadPair
#print axioms memV_of_writes
#print axioms memV_of_mem
#print axioms holds_drop1
#print axioms regionBytes_of_span
#print axioms memV_loads
#print axioms regionWord_of_bytes
end ArmCertValue.Physical
