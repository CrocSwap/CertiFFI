import XlateSecp.World
import ReleaseProfile.GB10.WorldSemantics
import SecpMath.SubSSA
import TranslateSpan.SecpRawDeployment
import ArmCertValue.EntrySnapshot

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# secp Runtime10 statics over XlateSecp.World (shared lemmas; speed mode: compiles, not verified)

The world entry's memory is `Std.ExtHashMap.ofList World.plan`. With the plan keys distinct (Xlate's `World.planKeys`)
every memory read of the entry is `plan.lookup`.
-/

namespace ReleaseProfile.GB10.SecpRuntime.Statics

open ReleaseProfile.MachineSource ReleaseProfile.GB10

theorem keys_pairwise : XlateSecp.World.plan.Pairwise (fun a b => (a.1 == b.1) = false) := XlateSecp.World.planKeys

theorem lookup_some_mem {pa : Nat} {v : BitVec 8} : ∀ l : List (Nat × BitVec 8), l.lookup pa = some v → (pa, v) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, b) :: t, h => by
    by_cases e : pa = k
    · subst e; simp [List.lookup] at h; subst h; exact List.mem_cons_self
    · have : (pa == k) = false := by simpa using e
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_some_mem t h)

theorem lookup_none_ne {pa : Nat} : ∀ l : List (Nat × BitVec 8), l.lookup pa = none → ∀ q ∈ l, q.1 ≠ pa
  | [], _, _, hq => by simp at hq
  | (k, b) :: t, h, q, hq => by
    by_cases e : pa = k
    · subst e; simp [List.lookup] at h
    · have : (pa == k) = false := by simpa using e
      simp only [List.lookup, this] at h
      rcases List.mem_cons.1 hq with rfl | hq
      · exact fun h' => e h'.symm
      · exact lookup_none_ne t h q hq

variable (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
  (card : XlateSecp.World.Card) (pcount : BitVec 88)

/-- Every entry memory read is the plan lookup. -/
theorem mem_eq (pa : Nat) :
    (XlateSecp.World.entry sem rho caller card pcount).mem[pa]? = XlateSecp.World.plan.lookup pa := by
  show (Std.ExtHashMap.ofList XlateSecp.World.plan)[pa]? = _
  cases hl : XlateSecp.World.plan.lookup pa with
  | none =>
    apply Std.ExtHashMap.getElem?_ofList_of_contains_eq_false
    simp only [List.contains_eq_any_beq, List.any_eq_false, List.mem_map, beq_iff_eq]
    rintro _ ⟨q, hm, rfl⟩ e
    exact lookup_none_ne _ hl q hm e.symm
  | some v =>
    have hm : (pa, v) ∈ XlateSecp.World.plan := lookup_some_mem _ hl
    exact Std.ExtHashMap.getElem?_ofList_of_mem (k := pa) (BEq.refl _) keys_pairwise hm

/-- The entry's GPRs are the world data's. -/
theorem gpr_eq : (XlateSecp.World.entry sem rho caller card pcount).regs.gpr = (XlateSecp.World.data card).gpr := rfl



/-- Split a Bool `all` over a list into `take n` / `drop n` (keeps each kernel `decide` small). -/
theorem all_of_take_drop {α : Type} (f : α → Bool) (l : List α) (n : Nat)
    (h1 : (l.take n).all f = true) (h2 : (l.drop n).all f = true) : l.all f = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2]; rfl

/-! ## Inputs: zero buffers -/

theorem limbs_congr (l1 l2 : List (BitVec 64)) (s : Nat)
    (h : ∀ t, s ≤ t → t < s + 32 → l1.getD t 0 = l2.getD t 0) :
    SecpMath.SubSSA.inputLimbs l1 s = SecpMath.SubSSA.inputLimbs l2 s := by
  simp only [SecpMath.SubSSA.inputLimbs, SecpMath.SubSSA.inputWord, SecpMath.SubSSA.inputWordDef,
    ArmCertValue.Def.eval, List.map, ArmCertValue.Arg.eval]
  simp (disch := omega) only [h]

theorem word_nil (s : Nat) : SecpMath.SubSSA.inputWord [] s = 0 := by
  simp only [SecpMath.SubSSA.inputWord, SecpMath.SubSSA.inputWordDef, ArmCertValue.Def.eval, List.map,
    ArmCertValue.Arg.eval, List.getD_nil]
  decide

theorem limbs_nil (s : Nat) : (SecpMath.SubSSA.inputLimbs [] s).value < SecpMath.modulus := by
  simp only [SecpMath.SubSSA.inputLimbs, word_nil, SecpMath.LimbWords.value, SecpMath.pack4, BitVec.toNat_zero,
    Nat.mul_zero, Nat.add_zero]
  unfold SecpMath.modulus; decide

/-- Closed: the 32 bytes of region `r` (world data GPRs of `card`) map to zero plan bytes. -/
def RegZero (card : XlateSecp.World.Card) (r : ArmCertValue.Region) : Prop := ∀ t : Nat, t < 32 →
  ((XlateSecp.World.mapping (Sail.BitVec.addInt
      (if h : r.pin < 31 then (XlateSecp.World.data card).gpr[r.pin] else 0) (r.off + (t : Int)))).bind
    fun pa => List.lookup pa XlateSecp.World.plan).getD 0 = 0

theorem snapshot_zero (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (card : XlateSecp.World.Card) (pcount : BitVec 88) (norm : ArmCertValue.Region → ArmCertValue.Region) :
    ∀ (rs : List (ArmCertValue.Region × Nat)), (∀ x ∈ rs, x.2 = 32 ∧ RegZero card (norm x.1)) → ∀ t,
      ArmCertValue.Physical.Entry.snapshot
        (fun r j => XlateSecp.World.mapping (TranslateSpan.SecpRawDeployment.regionVA
          (XlateSecp.World.entry sem rho caller card pcount) (norm r) j))
        (XlateSecp.World.entry sem rho caller card pcount) rs t = 0
  | [], _, t => rfl
  | (r, n) :: rest, h, t => by
    obtain ⟨hn, hz⟩ := h (r, n) List.mem_cons_self
    simp only at hn; subst hn
    simp only [ArmCertValue.Physical.Entry.snapshot]
    split
    · rename_i ht
      simp only [ArmCertValue.Physical.regionByte, TranslateSpan.SecpRawDeployment.regionVA,
        TranslateSpan.SecpRawDeployment.entryGPR, gpr_eq, mem_eq]
      exact hz t ht
    · exact snapshot_zero sem rho caller card pcount norm rest (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

end ReleaseProfile.GB10.SecpRuntime.Statics

#print axioms ReleaseProfile.GB10.SecpRuntime.Statics.mem_eq
