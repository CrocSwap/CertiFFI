module

public import ArmCert.Leakage.Machine

set_option autoImplicit false

@[expose] public section

/-!
# CT0/CT1 observation transport — generic, ISA-neutral layer

Source machine `N` (intended: frozen ArmSpec native step with the v2.2 observation
extraction) and target machine `L` (intended: CertiFFI `AArch64.Leakage.machine`
over LNSym). `p` projects states (intended: `ArmBridge.Draft.project` d2a15afe,
extended as needed), `q` projects native observations onto target observations
(intended: v2.2 contract fields → `Leakage.Observation`).

The only per-ISA obligation is `StepSimulation`: on every admitted native state,
a successful native step is matched by a successful target step on the projected
state, with projected successor and projected observation, and admission is
preserved. That obligation is NOT discharged here; it is the per-form work (O1).

Results: run-level forward simulation (exact count and first-return), and the
transport of the CT0 trace-equality and CT1 DIT obligations from the target to
the projected native traces. Nothing here asserts any certificate exists.
-/

namespace ArmCertCT

open CertiFFI.Leakage

variable {NS NO LS LO : Type}

/-- Per-step forward simulation on the admitted native domain. -/
def StepSimulation (N : Machine NS NO) (L : Machine LS LO)
    (p : NS → LS) (q : NO → LO) (admitted : NS → Prop) : Prop :=
  ∀ s s' o, admitted s → N.step s = some (s', o) →
    admitted s' ∧ L.step (p s) = some (p s', q o)

section
variable {N : Machine NS NO} {L : Machine LS LO} {p : NS → LS} {q : NO → LO}
  {admitted : NS → Prop}

theorem run_forward (sim : StepSimulation N L p q admitted) :
    ∀ (count : Nat) (s f : NS) (trace : List NO), admitted s →
      run N count s = some (f, trace) →
      admitted f ∧ run L count (p s) = some (p f, trace.map q)
  | 0, s, f, trace, adm, h => by
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨adm, rfl⟩
  | count + 1, s, f, trace, adm, h => by
      simp only [run] at h
      cases hs : N.step s with
      | none => simp [hs] at h
      | some pair =>
        obtain ⟨s', o⟩ := pair
        cases hr : run N count s' with
        | none => simp [hs, hr] at h
        | some pair' =>
          obtain ⟨f', t'⟩ := pair'
          simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨adm', hl⟩ := sim s s' o adm hs
          obtain ⟨admf, ih⟩ := run_forward sim count s' f' t' adm' hr
          refine ⟨admf, ?_⟩
          simp [run, hl, ih]

theorem runUntil_forward (sim : StepSimulation N L p q admitted) (stop : LS → Bool) :
    ∀ (count : Nat) (s f : NS) (trace : List NO), admitted s →
      runUntil N (fun x => stop (p x)) count s = some (f, trace) →
      admitted f ∧ runUntil L stop count (p s) = some (p f, trace.map q)
  | 0, s, f, trace, adm, h => by
      by_cases hstop : stop (p s) = true
      · simp only [runUntil, hstop, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨adm, by simp [runUntil, hstop]⟩
      · simp [runUntil, hstop] at h
  | count + 1, s, f, trace, adm, h => by
      by_cases hstop : stop (p s) = true
      · simp only [runUntil, hstop, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨adm, by simp [runUntil, hstop]⟩
      · simp only [runUntil, hstop, Bool.false_eq_true, ite_false] at h
        cases hs : N.step s with
        | none => simp [hs] at h
        | some pair =>
          obtain ⟨s', o⟩ := pair
          cases hr : runUntil N (fun x => stop (p x)) count s' with
          | none => simp [hs, hr] at h
          | some pair' =>
            obtain ⟨f', t'⟩ := pair'
            simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨adm', hl⟩ := sim s s' o adm hs
            obtain ⟨admf, ih⟩ := runUntil_forward sim stop count s' f' t' adm' hr
            refine ⟨admf, ?_⟩
            simp [runUntil, hstop, hl, ih]

/-- CT0 trace transport: if the target's executions from projected initial
states have equal traces (the target CT0 `constantTrace` instantiated at these
two runs), the native traces are equal after observation projection. -/
theorem ct0_trace_transport (sim : StepSimulation N L p q admitted)
    {cl cr : Nat} {sl sr fl fr : NS} {tl tr : List NO}
    (al : admitted sl) (ar : admitted sr)
    (hl : run N cl sl = some (fl, tl)) (hr : run N cr sr = some (fr, tr))
    (targetCT0 : ∀ {fl' fr' : LS} {tl' tr' : List LO},
      run L cl (p sl) = some (fl', tl') → run L cr (p sr) = some (fr', tr') → tl' = tr') :
    tl.map q = tr.map q :=
  targetCT0 (run_forward sim cl sl fl tl al hl).2 (run_forward sim cr sr fr tr ar hr).2

/-- Same, first-return boundary (`RunBoundary.firstReturn`). -/
theorem ct0_trace_transport_until (sim : StepSimulation N L p q admitted) (stop : LS → Bool)
    {cl cr : Nat} {sl sr fl fr : NS} {tl tr : List NO}
    (al : admitted sl) (ar : admitted sr)
    (hl : runUntil N (fun x => stop (p x)) cl sl = some (fl, tl))
    (hr : runUntil N (fun x => stop (p x)) cr sr = some (fr, tr))
    (targetCT0 : ∀ {fl' fr' : LS} {tl' tr' : List LO},
      runUntil L stop cl (p sl) = some (fl', tl') →
      runUntil L stop cr (p sr) = some (fr', tr') → tl' = tr') :
    tl.map q = tr.map q :=
  targetCT0 (runUntil_forward sim stop cl sl fl tl al hl).2
    (runUntil_forward sim stop cr sr fr tr ar hr).2

/-- CT1 DIT-eligibility transport: every projected native observation of an
admitted run is eligible when every target observation of the matched run is. -/
theorem ct1_eligible_transport (sim : StepSimulation N L p q admitted)
    (eligible : LO → Prop) {count : Nat} {s f : NS} {trace : List NO}
    (adm : admitted s) (h : run N count s = some (f, trace))
    (target : ∀ {f' : LS} {t' : List LO}, run L count (p s) = some (f', t') →
      ∀ o ∈ t', eligible o) :
    ∀ o ∈ trace, eligible (q o) := by
  intro o mem
  exact target (run_forward sim count s f trace adm h).2 (q o) (List.mem_map_of_mem mem)

/-- CT1 DIT-enabled transport: every native prefix state of an admitted run
projects to a target prefix state, so the target's `enabled` obligation (read
through `p`) holds on every native prefix. -/
theorem ct1_enabled_transport (sim : StepSimulation N L p q admitted)
    (enabled : LS → Prop) {s : NS}
    (adm : admitted s)
    (target : ∀ (k : Nat) (cur : LS) (front : List LO),
      run L k (p s) = some (cur, front) → enabled cur) :
    ∀ (k : Nat) (cur : NS) (front : List NO),
      run N k s = some (cur, front) → enabled (p cur) := by
  intro k cur front h
  exact target k (p cur) (front.map q) (run_forward sim k s cur front adm h).2

/-- Native-side CT1 enabled predicate (: DIT stays OUT of the sealed
projection d2a15afe and is read from the native state, e.g. `s.regs.PSTATE.DIT`).
If admission implies DIT enabled and the step simulation preserves admission
(determines `s'.regs.PSTATE` exactly per form), every native prefix
state of an admitted run is DIT-enabled. -/
theorem ct1_enabled_native (sim : StepSimulation N L p q admitted)
    (enabled : NS → Prop) (hEn : ∀ s, admitted s → enabled s) {s : NS}
    (adm : admitted s) :
    ∀ (k : Nat) (cur : NS) (front : List NO),
      run N k s = some (cur, front) → enabled cur := by
  intro k cur front h
  exact hEn cur (run_forward sim k s cur front adm h).1

/-- Full-trace recovery: if every observation an admitted native step emits is
recoverable from its target projection (`o = r (q o)`, e.g. the derived walk/fetch
events are a fixed public function of the target observation), the native trace is
determined by its projection. -/
theorem trace_recover (sim : StepSimulation N L p q admitted) (r : LO → NO)
    (rec : ∀ s s' o, admitted s → N.step s = some (s', o) → o = r (q o)) :
    ∀ (count : Nat) (s f : NS) (trace : List NO), admitted s →
      run N count s = some (f, trace) → trace = (trace.map q).map r
  | 0, s, f, trace, adm, h => by
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
  | count + 1, s, f, trace, adm, h => by
      simp only [run] at h
      cases hs : N.step s with
      | none => simp [hs] at h
      | some pair =>
        obtain ⟨s', o⟩ := pair
        cases hr : run N count s' with
        | none => simp [hs, hr] at h
        | some pair' =>
          obtain ⟨f', t'⟩ := pair'
          simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ih := trace_recover sim r rec count s' f' t' (sim s s' o adm hs).1 hr
          simp only [List.map_cons]
          rw [← rec s s' o adm hs, ← ih]

/-- CT0 for the FULL native trace (not only its projection), given recovery. -/
theorem ct0_full_transport (sim : StepSimulation N L p q admitted) (r : LO → NO)
    (rec : ∀ s s' o, admitted s → N.step s = some (s', o) → o = r (q o))
    {cl cr : Nat} {sl sr fl fr : NS} {tl tr : List NO}
    (al : admitted sl) (ar : admitted sr)
    (hl : run N cl sl = some (fl, tl)) (hr : run N cr sr = some (fr, tr))
    (targetCT0 : ∀ {fl' fr' : LS} {tl' tr' : List LO},
      run L cl (p sl) = some (fl', tl') → run L cr (p sr) = some (fr', tr') → tl' = tr') :
    tl = tr := by
  rw [trace_recover sim r rec cl sl fl tl al hl, trace_recover sim r rec cr sr fr tr ar hr,
    ct0_trace_transport sim al ar hl hr targetCT0]

/-- Adapter for the consumer's per-path CT0 shape (certiffi C35CT 1ea00365):
`∃ trace, run L n left = some (_, trace) ∧ run L n right = some (_, trace)` yields
the `targetCT0` hypothesis of `ct0_trace_transport` / `ct0_full_transport`. -/
theorem targetCT0_of_exists {n : Nat} {l r : LS}
    (h : ∃ (fl fr : LS) (trace : List LO), run L n l = some (fl, trace) ∧ run L n r = some (fr, trace)) :
    ∀ {fl' fr' : LS} {tl' tr' : List LO},
      run L n l = some (fl', tl') → run L n r = some (fr', tr') → tl' = tr' := by
  intro fl' fr' tl' tr' hl hr
  obtain ⟨fl, fr, trace, h1, h2⟩ := h
  rw [h1] at hl; rw [h2] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hl hr
  rw [← hl.2, ← hr.2]

/-- Observation-mapped machine (e.g. CertiFFI `Leakage.Observation` → isla's field-for-field
mirror). -/
def mapObs {S O O' : Type} (f : O → O') (M : Machine S O) : Machine S O' :=
  ⟨fun s => (M.step s).map fun x => (x.1, f x.2)⟩

theorem run_mapObs {S O O' : Type} (f : O → O') (M : Machine S O) :
    ∀ (n : Nat) (s : S), run (mapObs f M) n s = (run M n s).map fun x => (x.1, x.2.map f)
  | 0, s => rfl
  | n + 1, s => by
      have ih := run_mapObs f M n
      have hs : (mapObs f M).step s = (M.step s).map (fun x => (x.1, f x.2)) := rfl
      simp only [run]
      rw [hs]
      cases h : M.step s with
      | none => simp
      | some x =>
        obtain ⟨s', o⟩ := x
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        rw [ih s']
        cases run M n s' <;> simp

/-- CT0 (per-path, some-runs form) transfers to the mapped machine. -/
theorem targetCT0_mapObs {S O O' : Type} (f : O → O') (M : Machine S O) {n : Nat} {l r : S}
    (h : ∃ (fl fr : S) (trace : List O), run M n l = some (fl, trace) ∧ run M n r = some (fr, trace)) :
    ∃ (fl fr : S) (trace : List O'), run (mapObs f M) n l = some (fl, trace) ∧
      run (mapObs f M) n r = some (fr, trace) := by
  obtain ⟨fl, fr, trace, h1, h2⟩ := h
  exact ⟨fl, fr, trace.map f, by rw [run_mapObs, h1]; rfl, by rw [run_mapObs, h2]; rfl⟩

/-- run_rel (eval fc2c: isla owns the CT2 B1 run-level lift). Any reflexive-transitive relation
that holds across every admitted step of a machine holds from the start to the end of an exact
n-step run, under eval's INDEXED admission (`Adm (k+1) s → step → Adm k s'`). -/
theorem run_rel {S O : Type} (M : Machine S O) (R : S → S → Prop)
    (hrefl : ∀ s, R s s) (htrans : ∀ a b c, R a b → R b c → R a c) (Adm : Nat → S → Prop)
    (hstep : ∀ k s s' o, Adm (k + 1) s → M.step s = some (s', o) → R s s' ∧ Adm k s') :
    ∀ (n : Nat) (s f : S) (t : List O), Adm n s → run M n s = some (f, t) → R s f
  | 0, s, f, t, _, h => by
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; exact hrefl s
  | n + 1, s, f, t, adm, h => by
      simp only [run] at h
      cases hs : M.step s with
      | none => simp [hs] at h
      | some pair =>
        obtain ⟨s', o⟩ := pair
        cases hr : run M n s' with
        | none => simp [hs, hr] at h
        | some pair' =>
          obtain ⟨f', t'⟩ := pair'
          simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          obtain ⟨hR, adm'⟩ := hstep n s s' o adm hs
          exact htrans _ _ _ hR (run_rel M R hrefl htrans Adm hstep n s' f' t' adm' hr)

end
end ArmCertCT

#print axioms ArmCertCT.run_rel
