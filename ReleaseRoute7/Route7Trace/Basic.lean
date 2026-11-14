-- Route 7 CT0 (loops): per-tick event traces of a run and the two-run timing theorem. `Traced` says every step of a
-- `ticks`-step run from `x` starts at the scheduled PC and has the scheduled (public) data records; two traced runs
-- with the same schedule and equal final PCs have equal ordered V2 event records (PhasedCT.TimingRec),.
import Route7Copy.Cover
import Bridge.CruxGenGuarded.StepEvents
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace Route7Trace
open ArmCertLoop

abbrev Recs := Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)

/-- Every step j < ticks of the run from x starts at pcAt (off + j) with event shape recs (off + j), and keeps the
    scalar non-projected register frame (`Effects.Frame {}`: in particular PSTATE.DIT; CT1 P1). -/
def Traced (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (recs : Recs) (pcAt : Nat → BitVec 64) (ticks off : Nat) (x : NativeState) : Prop :=
  ∀ j, j < ticks → ∃ z z', Uget.Chain.modelRun real j x = .ok () z ∧ modelStep real z = .ok () z' ∧
    z.regs._PC = pcAt (off + j) ∧ StepEvents.EvShape spec mapping (recs (off + j)) z z' ∧
    NativeEntry.Effects.Frame {} z.regs z'.regs

/-- CT1: a scalar frame step keeps PSTATE.DIT. -/
theorem dit_of_frame {a b : Regs} (h : NativeEntry.Effects.Frame {} a b) : b.PSTATE.DIT = a.PSTATE.DIT := by
  have equal := congrArg (fun r : Regs => r.PSTATE.DIT) h
  simpa [NativeEntry.Effects.mask, NativeEntry.Effects.erase, ArmCertCT.CT2.mask, ArmCertCT.CT2.maskPSTATE] using equal

section
variable (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
  (mapping : BitVec 64 → Option Nat) (recs : Recs) (pcAt : Nat → BitVec 64)

theorem run_one (x y : NativeState) (step : modelStep real x = .ok () y) :
    Uget.Chain.modelRun real 1 x = .ok () y := by
  simp only [Uget.Chain.modelRun, step]

theorem traced_zero (off : Nat) (x : NativeState) : Traced real spec mapping recs pcAt 0 off x := by
  intro j hj; omega

/-- One step with its scheduled PC and records. -/
theorem traced_one (off : Nat) (x y : NativeState) (step : modelStep real x = .ok () y)
    (pc : x.regs._PC = pcAt off) (ev : StepEvents.EvShape spec mapping (recs off) x y)
    (frame : NativeEntry.Effects.Frame {} x.regs y.regs) :
    Traced real spec mapping recs pcAt 1 off x := by
  intro j hj
  have : j = 0 := by omega
  subst this
  exact ⟨x, y, rfl, step, by simpa using pc, by simpa using ev, frame⟩

theorem traced_append (n m off : Nat) (x y : NativeState) (run : Uget.Chain.modelRun real n x = .ok () y)
    (first : Traced real spec mapping recs pcAt n off x) (second : Traced real spec mapping recs pcAt m (off + n) y) :
    Traced real spec mapping recs pcAt (n + m) off x := by
  intro j hj
  by_cases low : j < n
  · exact first j low
  · obtain ⟨z, z', rz, sz, pz, ez, fz⟩ := second (j - n) (by omega)
    have idx : off + n + (j - n) = off + j := by omega
    refine ⟨z, z', ?_, sz, by rw [pz, idx], by rw [← idx]; exact ez, fz⟩
    have := Aux.modelRun_append real n (j - n) x y z run rz
    rwa [Nat.add_sub_cancel' (Nat.le_of_not_lt low)] at this

/-- **Two-run timing**: two runs traced against the same public schedule (PCs + data records)
whose final states have equal PCs have equal record traces over the whole run. -/
theorem ct_of_traced (N : Nat) (e1 e2 f1 f2 : NativeState)
    (t1 : Traced real spec mapping recs pcAt N 0 e1) (t2 : Traced real spec mapping recs pcAt N 0 e2)
    (run1 : Uget.Chain.modelRun real N e1 = .ok () f1) (run2 : Uget.Chain.modelRun real N e2 = .ok () f2)
    (pcEnd : f1.regs._PC = f2.regs._PC) (pc0 : e1.regs._PC = e2.regs._PC) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 N) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 N) := by
  have s0 : ∀ e : NativeState, CertiFFI.Prog.Generic.ModelRunView.stateAt real e 0 = e := fun e =>
    CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real 0 e e rfl
  have := PhasedCT.phased_records (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1)
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2) (fun _ _ _ => True) N trivial
    (by rw [s0, s0]; exact pc0) ?_
  · rwa [s0, s0] at this
  intro k hk _
  refine ⟨?_, trivial⟩
  obtain ⟨z1, z1', r1, st1, p1, ev1, -⟩ := t1 k hk
  obtain ⟨z2, z2', r2, st2, p2, ev2, -⟩ := t2 k hk
  simp only [Nat.zero_add] at p1 p2 ev1 ev2
  have k1 : ∀ e z z', Uget.Chain.modelRun real k e = .ok () z → modelStep real z = .ok () z' →
      CertiFFI.Prog.Generic.ModelRunView.stateAt real e (k + 1) = z' := fun e z z' r s =>
    CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (k + 1) e z'
      (Aux.modelRun_append real k 1 e z z' r (run_one real z z' s))
  rw [CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real k e1 z1 r1,
    CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real k e2 z2 r2, k1 e1 z1 z1' r1 st1, k1 e2 z2 z2' r2 st2]
  refine StepEvents.pair spec mapping (recs k) z1 z2 z1' z2' ev1 ev2 (p1.trans p2.symm) ?_
  by_cases more : k + 1 < N
  · obtain ⟨y1, _, ry1, _, py1, _, _⟩ := t1 (k + 1) more
    obtain ⟨y2, _, ry2, _, py2, _, _⟩ := t2 (k + 1) more
    have a1 := Aux.modelRun_append real k 1 e1 z1 z1' r1 (run_one real z1 z1' st1)
    have a2 := Aux.modelRun_append real k 1 e2 z2 z2' r2 (run_one real z2 z2' st2)
    rw [a1] at ry1; rw [a2] at ry2
    cases ry1; cases ry2
    simp only [Nat.zero_add] at py1 py2
    exact py1.trans py2.symm
  · have last : k + 1 = N := by omega
    have a1 := Aux.modelRun_append real k 1 e1 z1 z1' r1 (run_one real z1 z1' st1)
    have a2 := Aux.modelRun_append real k 1 e2 z2 z2' r2 (run_one real z2 z2' st2)
    rw [last, run1] at a1; rw [last, run2] at a2
    cases a1; cases a2
    exact pcEnd
end

/-- CT1 P1 input: along a traced run every step keeps PSTATE.DIT (CT1.DitWindow.Preserves over stateAt). -/
theorem dit_preserved (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (recs : Recs) (pcAt : Nat → BitVec 64) (N : Nat) (e : NativeState)
    (t : Traced real spec mapping recs pcAt N 0 e) :
    ∀ j, j < N → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (j + 1)).regs.PSTATE.DIT =
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e j).regs.PSTATE.DIT := by
  intro j hj
  obtain ⟨z, z', rz, sz, -, -, fz⟩ := t j hj
  rw [CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real j e z rz,
    CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (j + 1) e z'
      (Aux.modelRun_append real j 1 e z z' rz (run_one real z z' sz))]
  exact dit_of_frame fz

end Route7Trace
#print axioms Route7Trace.traced_append
#print axioms Route7Trace.ct_of_traced
#print axioms Route7Trace.dit_preserved
