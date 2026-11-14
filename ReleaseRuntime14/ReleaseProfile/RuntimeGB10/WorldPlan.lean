-- Runtime world entry RAM plan (clean names; adapted from R14Init.Plan / R14Witness.Plan, d200 P2(B)):
-- the closure code bytes (R14LoaderSynth.codePlan, square.elf 55b0e3bf) at 0x80100000 + image offset,
-- the world page-table rows (ReleaseProfile.RuntimeGB10.World.imageRows) and per-case data bytes.
import ReleaseProfile.RuntimeGB10.World
import R14LoaderSynth.CodePlan
import ArmCertTranslateModel.PlanChecks
set_option autoImplicit false
set_option maxRecDepth 100000
namespace ReleaseProfile.RuntimeGB10.WorldPlan
open ArmCert.Translate.Model

/-- Page-table rows of the world tables, as physical bytes. -/
def tableRows : NativeSourceInit.Plan := imageRowsPlan ReleaseProfile.RuntimeGB10.World.imageRows

/-- Data PA ranges: x1obj, x0obj, payload, x19obj (64 bytes each) and the stack frame [SP-64, SP). -/
def dataRanges : List (Nat × Nat) :=
  [(0x80600000, 64), (0x80601000, 64), (0x80602000, 64), (0x80604000, 64), (0x80603fc0, 64)]

def dataAddrs : List Nat := dataRanges.flatMap fun r => (List.range r.2).map fun i => r.1 + i

/-- Per-case data bytes `db` at the data addresses. -/
def dataPlan (db : Nat → BitVec 8) : NativeSourceInit.Plan := dataAddrs.map fun a => (a, db a)

def plan (db : Nat → BitVec 8) : NativeSourceInit.Plan := R14LoaderSynth.codePlan ++ tableRows ++ dataPlan db

theorem table_nodup : (tableRows.map (·.1)).Nodup := by decide +kernel
theorem table_range : tableRows.all (fun r => decide (0x80000000 ≤ r.1 ∧ r.1 < 0x80005000)) = true := by decide +kernel
theorem addrs_nodup : dataAddrs.Nodup := by decide +kernel
theorem addrs_range : dataAddrs.all (fun a => decide (0x80600000 ≤ a ∧ a < 0x80605000)) = true := by decide +kernel

theorem data_nodup (db : Nat → BitVec 8) : ((dataPlan db).map (·.1)).Nodup := by
  simpa only [dataPlan, List.map_map, Function.comp_def, List.map_id'] using addrs_nodup

theorem data_range (db : Nat → BitVec 8) :
    (dataPlan db).all (fun r => decide (0x80600000 ≤ r.1 ∧ r.1 < 0x80605000)) = true := by
  simpa only [dataPlan, List.all_map, Function.comp_def] using addrs_range

theorem disjoint_of_ranges (l1 l2 : NativeSourceInit.Plan) (lo1 hi1 lo2 hi2 : Nat)
    (h1 : l1.all (fun r => decide (lo1 ≤ r.1 ∧ r.1 < hi1)) = true) (h2 : l2.all (fun r => decide (lo2 ≤ r.1 ∧ r.1 < hi2)) = true)
    (sep : hi1 ≤ lo2 ∨ hi2 ≤ lo1) : ∀ a, a ∈ l1.map (·.1) → a ∉ l2.map (·.1) := by
  intro a ha hb
  obtain ⟨r1, m1, e1⟩ := List.mem_map.1 ha
  obtain ⟨r2, m2, e2⟩ := List.mem_map.1 hb
  have c1 := of_decide_eq_true (List.all_eq_true.1 h1 r1 m1)
  have c2 := of_decide_eq_true (List.all_eq_true.1 h2 r2 m2)
  omega

theorem plan_nodup (db : Nat → BitVec 8) : ((plan db).map (·.1)).Nodup := by
  have hc := R14LoaderSynth.codePlan_range
  simp only [plan, List.map_append]
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨R14LoaderSynth.codePlan_nodup, table_nodup, ?_⟩, data_nodup db, ?_⟩
  · intro a ha b hb e; subst e; exact disjoint_of_ranges _ _ _ _ _ _ hc table_range (by omega) a ha hb
  · intro a ha b hb e; subst e
    rcases List.mem_append.1 ha with ha | ha
    · exact disjoint_of_ranges _ _ _ _ _ _ hc (data_range db) (by omega) a ha hb
    · exact disjoint_of_ranges _ _ _ _ _ _ table_range (data_range db) (by omega) a ha hb

theorem consistent_of_nodup (p : NativeSourceInit.Plan) (h : (p.map (·.1)).Nodup) : NativeSourceInit.Consistent p := by
  induction p with
  | nil => intro a ha; cases ha
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at h
    intro a ha b hb e
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (e ▸ List.mem_map_of_mem (f := (·.1)) hb') h.1
    · exact absurd (e.symm ▸ List.mem_map_of_mem (f := (·.1)) ha') h.1
    · exact ih h.2 a ha' b hb' e

theorem consistent (db : Nat → BitVec 8) : NativeSourceInit.Consistent (plan db) := consistent_of_nodup _ (plan_nodup db)

#print axioms consistent
end ReleaseProfile.RuntimeGB10.WorldPlan
