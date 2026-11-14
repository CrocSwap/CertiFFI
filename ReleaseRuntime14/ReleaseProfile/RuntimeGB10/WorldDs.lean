-- Runtime world data statics (clean names): R14Init.DsHpCore + R14Witness.Agree re-proved over
-- ReleaseProfile.RuntimeGB10.World.mapping/imageRows and WorldPlan.plan (same proofs, substituted constants).
import R14Init.Agree
import ReleaseProfile.RuntimeGB10.WorldStatics
import PipeR14Mem.Static
import ArmCertTranslateModel.C9Checks
set_option autoImplicit false
set_option maxRecDepth 100000
namespace ReleaseProfile.RuntimeGB10.WorldDs
open R14Init
open ArmCertValue ArmCert.Translate ArmCert.Translate.Model PipeR14

/-- The world page-table footprint as a Bool. -/
def fpB (a : Nat) : Bool := (ReleaseProfile.RuntimeGB10.World.imageRows.map (·.slot)).any fun sl => decide (sl ≤ a ∧ a < sl + 8)

theorem fp_of (a : Nat) (h : fpB a = false) : ¬ (rowsFootprint ReleaseProfile.RuntimeGB10.World.imageRows).byte a := by
  rintro ⟨sl, hs, lo, hi⟩
  have : fpB a = true := List.any_eq_true.2 ⟨sl, hs, by simp only [decide_eq_true_eq]; exact ⟨lo, hi⟩⟩
  rw [h] at this; cases this

/-- One data site: mapped below 2^56, not MMIO, off the tables, inside the data window, aligned, contiguous. -/
def siteOK (p : R14E17.Pins) (s : R14Plan.Base × Nat) : Bool :=
  match ReleaseProfile.RuntimeGB10.World.mapping (R14E17.dataVA p s.1) with
  | none => false
  | some n => decide (n < 2 ^ 56) && checkMappedNotMMIO ReleaseProfile.RuntimeGB10.World.mapping (R14E17.dataVA p s.1) &&
      (List.range s.2).all (fun t => !fpB (n + t)) && decide ((R14E17.dataVA p s.1).toNat % s.2 = 0) &&
      decide (0x80600000 ≤ n ∧ n + s.2 ≤ 0x80605000) &&
      (List.range s.2).all (fun t => ReleaseProfile.RuntimeGB10.World.mapping (R14E17.dataVA p s.1 + BitVec.ofNat 64 t) == some (n + t))

theorem site_of (p : R14E17.Pins) (s : R14Plan.Base × Nat) (h : siteOK p s = true) :
    ∃ pa : BitVec 56, ReleaseProfile.RuntimeGB10.World.mapping (R14E17.dataVA p s.1) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      (∀ t, t < s.2 → ¬ (rowsFootprint ReleaseProfile.RuntimeGB10.World.imageRows).byte (pa.toNat + t)) ∧
      (R14E17.dataVA p s.1).toNat % s.2 = 0 ∧
      (∀ t, t < s.2 → ReleaseProfile.RuntimeGB10.World.mapping (R14E17.dataVA p s.1 + BitVec.ofNat 64 t) = some (pa.toNat + t)) := by
  unfold siteOK at h
  cases hm : ReleaseProfile.RuntimeGB10.World.mapping (R14E17.dataVA p s.1) with
  | none => rw [hm] at h; cases h
  | some n =>
    rw [hm] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true',
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hn, hmm⟩, hfp⟩, hal⟩, _⟩, hc⟩ := h
    have e : (BitVec.ofNat 56 n).toNat = n := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    refine ⟨BitVec.ofNat 56 n, by rw [e], ?_, fun t ht => by rw [e]; exact fp_of _ (hfp t ht), hal,
      fun t ht => by rw [e]; exact hc t ht⟩
    exact checkMappedNotMMIO_sound hmm (BitVec.ofNat 56 n) (by rw [e]; exact hm)

theorem site_range (p : R14E17.Pins) (s : R14Plan.Base × Nat) (h : siteOK p s = true) {t a : Nat} (ht : t < s.2)
    (ha : ReleaseProfile.RuntimeGB10.World.mapping (R14E17.dataVA p s.1 + BitVec.ofNat 64 t) = some a) :
    0x80600000 ≤ a ∧ a < 0x80605000 := by
  unfold siteOK at h
  cases hm : ReleaseProfile.RuntimeGB10.World.mapping (R14E17.dataVA p s.1) with
  | none => rw [hm] at h; cases h
  | some n =>
    rw [hm] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hr⟩, hc⟩ := h
    rw [hc t ht] at ha; cases ha; omega

/-- Page of a world frame number (inverse of the world mapping's page table). -/
def invP (f : Nat) : Nat :=
  if f = 0x803b6 then 0x6b6 else if f = 0x803ba then 0x6ba else if f = 0x80491 then 0x791 else
  if f = 0x80600 then 0x30 else if f = 0x80601 then 0x31 else if f = 0x80602 then 0x32 else
  if f = 0x80604 then 0x33 else if f = 0x80603 then 0x1ff else 0

theorem fdiv (F o : Nat) (hF : F % 4096 = 0) (ho : o < 4096) : (F + o) / 4096 = F / 4096 := by omega
theorem fmod (F o : Nat) (hF : F % 4096 = 0) (ho : o < 4096) : (F + o) % 4096 = o := by omega

set_option maxHeartbeats 1000000 in
theorem mapping_spec {v : BitVec 64} {q : Nat} (h : ReleaseProfile.RuntimeGB10.World.mapping v = some q) :
    v.toNat = 4096 * invP (q / 4096) + q % 4096 := by
  have o := Nat.mod_lt v.toNat (show 4096 > 0 by decide)
  have d := Nat.div_add_mod v.toNat 4096
  simp only [ReleaseProfile.RuntimeGB10.World.mapping] at h
  repeat' (split at h)
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Option.some.injEq] at h
       subst h
       simp (disch := first | decide | omega) only [fdiv, fmod]
       simp (config := { decide := true }) [invP]
       omega)

/-- The world mapping is injective (page frames are distinct, offsets kept). -/
theorem mapping_inj {v1 v2 : BitVec 64} {q : Nat} (h1 : ReleaseProfile.RuntimeGB10.World.mapping v1 = some q)
    (h2 : ReleaseProfile.RuntimeGB10.World.mapping v2 = some q) : v1 = v2 :=
  BitVec.eq_of_toNat_eq ((mapping_spec h1).trans (mapping_spec h2).symm)

/-- A region byte held by the plan, read through mkInputsL at its table position. -/
theorem inByte_of_plan (pl : NativeSourceInit.Plan) (p : R14E17.Pins) (rs : List (Region × Nat)) (x : ArmBridge.Draft.NativeState)
    (hm : NativeSourceInit.Satisfies pl x.mem) (g : Region) (j i k : Nat) (hb : memBL rs 0 g j = some (i, k))
    (pa : Nat) (hpa : ReleaseProfile.RuntimeGB10.World.mapping (BitVec.ofInt 64 ((pinv p g.pin : Int) + g.off + j)) = some pa)
    (b : BitVec 8) (hpl : (pa, b) ∈ pl) :
    inByte rs (mkInputsL x rs (R14Init.bytesOf ReleaseProfile.RuntimeGB10.World.mapping (pinv p) x rs)) g j = b.setWidth 64 := by
  have hs := memBL_spec rs 0 g j i k hb
  unfold inByte; rw [hb]
  simp only [mkInputsL]
  rw [mkInputsG_getD _ _ _ _ (by omega)]
  unfold inputValG
  rw [if_pos (by omega)]
  unfold R14Init.bytesOf
  rw [posL_of_memBL rs 0 g j i k hb]
  simp only [regionByte, hpa, Option.bind_some, hm _ hpl, Option.getD_some]

/-- A pinned register input of mkInputsL (index totalL rs + i) is the register's value. -/
theorem inReg (rs : List (Region × Nat)) (x : ArmBridge.Draft.NativeState) (bytes : Nat → BitVec 8) (i : Nat) (hi : i < 31) :
    (mkInputsL x rs bytes).getD (totalL rs + i) 0 = x.regs.gpr[i] := by
  simp only [mkInputsL]
  rw [mkInputsG_getD _ _ _ _ (by omega)]
  unfold inputValG
  rw [if_neg (by omega), dif_pos (by omega)]
  simp [HeapV2StepCerts.RegBind.regVal]
theorem inSP (rs : List (Region × Nat)) (x : ArmBridge.Draft.NativeState) (bytes : Nat → BitVec 8) :
    (mkInputsL x rs bytes).getD (totalL rs + 31) 0 = x.regs.SP_EL0 := by
  simp only [mkInputsL]
  rw [mkInputsG_getD _ _ _ _ (by omega)]
  unfold inputValG
  rw [if_neg (by omega), dif_neg (by omega), if_pos rfl]
  rfl

#print axioms site_of
#print axioms mapping_inj
#print axioms inByte_of_plan
/-- Code PAs (closure scope) miss every data-site PA. -/
theorem dsCode (p : R14E17.Pins) (sites : List (R14Plan.Base × Nat)) (h : sites.all (siteOK p) = true) :
    ImageTableSeparated PipeR14.closureScope 0x400000#64 ReleaseProfile.RuntimeGB10.World.mapping
      (DataPA ReleaseProfile.RuntimeGB10.World.mapping p sites) := by
  intro offset pa inside hmap ⟨s, hs, t, ht, hq⟩
  obtain ⟨c, m, i, hi4, rfl⟩ := inside
  have ok := List.all_eq_true.1 (List.all_eq_true.1 ReleaseProfile.RuntimeGB10.WorldStatics.code_words_ok c m) i (List.mem_range.2 hi4)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at ok
  rw [ok.1] at hmap; cases hmap
  have hr := of_decide_eq_true (List.all_eq_true.1 R14LoaderSynth.codePlan_range _ ok.2)
  have hd := site_range p s (List.all_eq_true.1 h s hs) ht hq
  simp only at hr
  omega

theorem inj_of_nodup_map {α β : Type} (f : α → β) : ∀ (l : List α), (l.map f).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, ha, b, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (e ▸ List.mem_map_of_mem hb') h.1
    · exact absurd (e.symm ▸ List.mem_map_of_mem ha') h.1
    · exact inj_of_nodup_map f xs h.2 a ha' b hb' e

/-- All tracked (region, byte) pairs. -/
def allBytes (regions : List Region) : List (Region × Nat) :=
  regions.flatMap fun r => (List.range (8 * r.words)).map fun j => (r, j)

theorem distinct_of (p : R14E17.Pins) (regions : List Region)
    (h : ((allBytes regions).map fun rj => regionVA p rj.1 rj.2).Nodup) :
    ∀ r1 ∈ regions, ∀ r2 ∈ regions, ∀ j1 j2, j1 < 8 * r1.words → j2 < 8 * r2.words →
      regionVA p r1 j1 = regionVA p r2 j2 → r1 = r2 ∧ j1 = j2 := by
  intro r1 h1 r2 h2 j1 j2 hj1 hj2 e
  have m1 : (r1, j1) ∈ allBytes regions := List.mem_flatMap.2 ⟨r1, h1, List.mem_map.2 ⟨j1, List.mem_range.2 hj1, rfl⟩⟩
  have m2 : (r2, j2) ∈ allBytes regions := List.mem_flatMap.2 ⟨r2, h2, List.mem_map.2 ⟨j2, List.mem_range.2 hj2, rfl⟩⟩
  have := inj_of_nodup_map _ _ h _ m1 _ m2 e
  simp only [Prod.mk.injEq] at this
  exact this

/-- ds at the world deployment from the decided checks. -/
theorem ds_of (p : R14E17.Pins) (sites : List (R14Plan.Base × Nat)) (regions : List Region)
    (hs : sites.all (siteOK p) = true) (hsp : p.regs 31 % 16 = 0)
    (hd : ((allBytes regions).map fun rj => regionVA p rj.1 rj.2).Nodup) :
    DataStaticR14 ReleaseProfile.RuntimeGB10.World.mapping p (rowsFootprint ReleaseProfile.RuntimeGB10.World.imageRows).byte sites regions
      PipeR14.closureScope 0x400000#64 where
  site := fun s m => site_of p s (List.all_eq_true.1 hs s m)
  sp16 := hsp
  code := dsCode p sites hs
  inj := fun _ _ _ _ _ _ _ _ _ h1 h2 => mapping_inj h1 h2
  distinct := distinct_of p regions hd

#print axioms ds_of
open ArmCertValue

def byteInput (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (db : Nat → BitVec 8)
    (rs : List (Region × Nat)) (i : Nat) : BitVec 8 :=
  match posL rs 0 i with
  | some (g,j) => match mapping (BitVec.ofInt 64 ((pinv g.pin : Int) + g.off + j)) with
    | some pa => db pa
    | none => 0
  | none => 0

def coverageOK (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (db : Nat → BitVec 8)
    (rs : List (Region × Nat)) : Bool :=
  rs.all fun r => (List.range r.2).all fun j =>
    match mapping (BitVec.ofInt 64 ((pinv r.1.pin : Int) + r.1.off + j)) with
    | some pa => (ReleaseProfile.RuntimeGB10.WorldPlan.plan db).contains (pa,db pa)
    | none => false

theorem agreesAt_zero (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region)
    (rs : List (Region × Nat)) (steps : List StepV) (db : Nat → BitVec 8) (x : ArmBridge.Draft.NativeState)
    (hm : NativeSourceInit.Satisfies (ReleaseProfile.RuntimeGB10.WorldPlan.plan db) x.mem) (ok : coverageOK mapping pinv db rs = true) :
    ArmCertPipe.AgreesAt mapping pinv regions (σ0L rs) (mkInputsL x rs (byteInput mapping pinv db rs)) steps 0 x := by
  refine ArmCertPipe.agreesAt_zero (agrees_σ0L mapping pinv x rs _ ?_) ?_
  · intro g j i k h
    obtain ⟨nb, m, hj⟩ := memBL_mem rs 0 g j i k h
    have c := List.all_eq_true.1 (List.all_eq_true.1 ok (g,nb) m) j (List.mem_range.2 hj)
    simp only [byteInput, posL_of_memBL rs 0 g j i k h]
    unfold regionByte
    cases hp : mapping (BitVec.ofInt 64 ((pinv g.pin : Int) + g.off + j)) with
    | none => simp [hp] at c
    | some pa =>
      simp only [hp, Option.bind_some]
      simp only [hp, List.contains_iff_mem] at c
      exact hm (pa,db pa) c
  · simp only [mkInputsL, mkInputsG_length]; exact σ0L_bounded rs

end ReleaseProfile.RuntimeGB10.WorldDs
