import ArmCertCTNative.EventObservation
import ArmCertCT.ObservationTransport

/-!
# Event-delta native machine and the per-form obligation (isla, O1 v2)

Native observation per step = `{pc, word, nextPC, accesses}` where `accesses` is the
projected event delta (values dropped). The target observation has the same shape
(CertiFFI `AArch64.Leakage.Observation`). `EventFaithful` is the per-form obligation;
it yields the `StepSimulation` consumed by `ct0_trace_transport` /
`ct1_eligible_transport` / `ct1_enabled_native` with the identity projection on
observations (after the field-for-field `DataAccess` mirror).
-/

open Sail.ConcurrencyInterfaceV1 CertiFFI.Leakage

namespace ArmCertCT.Native

structure Observation where
  pc : BitVec 64
  word : BitVec 32
  nextPC : BitVec 64
  accesses : List DataAccess
  deriving DecidableEq, Repr

variable [Arch] {R : Type} {c : ChoiceSource} {LS : Type}

/-- Full native observation: the CertiFFI-v1-shaped part plus the derived events. -/
structure FullObservation where
  v1 : Observation
  derived : List DerivedRec

def deltaOf (s s' : SequentialState R c) : Array Event :=
  s'.events.extract s.events.size s'.events.size

/-- The native observed machine. `fetchWord`/`pcOf` read the native state; the
accesses and derived events come only from the appended events. -/
def eventMachine (nativeStep : SequentialState R c → Option (SequentialState R c))
    (pcOf : SequentialState R c → BitVec 64) (fetchWord : SequentialState R c → BitVec 32) :
    Machine (SequentialState R c) FullObservation :=
  ⟨fun s => (nativeStep s).map fun s' =>
    (s', ⟨Observation.mk (pcOf s) (fetchWord s) (pcOf s') (obsAccesses (deltaOf s s')),
          derivedOf (deltaOf s s')⟩)⟩

/-- Per-form obligation. `walk` is a FIXED public function (instantiated per
profile with the admitted page map) from (pc, data accesses) to the derived events. -/
structure EventFaithful (nativeStep : SequentialState R c → Option (SequentialState R c))
    (pcOf : SequentialState R c → BitVec 64) (fetchWord : SequentialState R c → BitVec 32)
    (walk : BitVec 64 → List DataAccess → List DerivedRec)
    (L : Machine LS Observation) (p : SequentialState R c → LS)
    (admitted : SequentialState R c → Prop) : Prop where
  preserves : ∀ s s', admitted s → nativeStep s = some s' → admitted s'
  appendOnly : ∀ s s', admitted s → nativeStep s = some s' →
    ∃ delta, Appended s s' delta ∧ NoOtherEvents delta
  derivedPublic : ∀ s s', admitted s → nativeStep s = some s' →
    derivedOf (deltaOf s s') = walk (pcOf s) (obsAccesses (deltaOf s s'))
  simulates : ∀ s s', admitted s → nativeStep s = some s' →
    L.step (p s) = some (p s', Observation.mk (pcOf s) (fetchWord s) (pcOf s')
      (obsAccesses (deltaOf s s')))

section
variable {nativeStep : SequentialState R c → Option (SequentialState R c)}
    {pcOf : SequentialState R c → BitVec 64} {fetchWord : SequentialState R c → BitVec 32}
    {walk : BitVec 64 → List DataAccess → List DerivedRec}
    {L : Machine LS Observation} {p : SequentialState R c → LS}
    {admitted : SequentialState R c → Prop}

theorem EventFaithful.stepSimulation (f : ArmCertCT.Native.EventFaithful nativeStep pcOf fetchWord walk L p admitted) :
    ArmCertCT.StepSimulation (eventMachine nativeStep pcOf fetchWord) L p FullObservation.v1 admitted := by
  intro s s' o adm h
  simp only [eventMachine, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨s'', hs, rfl, rfl⟩ := h
  exact ⟨f.preserves s s'' adm hs, f.simulates s s'' adm hs⟩

/-- Recovery: every emitted full observation is determined by its v1 part. -/
theorem EventFaithful.recover (f : ArmCertCT.Native.EventFaithful nativeStep pcOf fetchWord walk L p admitted) :
    ∀ s s' o, admitted s → (eventMachine nativeStep pcOf fetchWord).step s = some (s', o) →
      o = (fun v : Observation => FullObservation.mk v (walk v.pc v.accesses)) o.v1 := by
  intro s s' o adm h
  simp only [eventMachine, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨s'', hs, rfl, rfl⟩ := h
  exact congrArg (FullObservation.mk _) (f.derivedPublic s s'' adm hs)

/-- CT0 for the FULL native event-delta trace: equal target (CertiFFI v1) traces
give equal native traces, derived walk/fetch events included. -/
theorem EventFaithful.ct0_full (f : ArmCertCT.Native.EventFaithful nativeStep pcOf fetchWord walk L p admitted)
    {cl cr : Nat} {sl sr fl fr : SequentialState R c} {tl tr : List FullObservation}
    (al : admitted sl) (ar : admitted sr)
    (hl : CertiFFI.Leakage.run (eventMachine nativeStep pcOf fetchWord) cl sl = some (fl, tl))
    (hr : CertiFFI.Leakage.run (eventMachine nativeStep pcOf fetchWord) cr sr = some (fr, tr))
    (targetCT0 : ∀ {fl' fr' : LS} {tl' tr' : List Observation},
      CertiFFI.Leakage.run L cl (p sl) = some (fl', tl') →
      CertiFFI.Leakage.run L cr (p sr) = some (fr', tr') → tl' = tr') :
    tl = tr :=
  ArmCertCT.ct0_full_transport f.stepSimulation
    (fun v : Observation => FullObservation.mk v (walk v.pc v.accesses)) f.recover al ar hl hr targetCT0

end

/-- The extracted delta is the appended one. -/
theorem extract_of_appended {s s' : SequentialState R c} {delta : Array Event}
    (h : Appended s s' delta) :
    s'.events.extract s.events.size s'.events.size = delta := by
  unfold Appended at h
  rw [h]
  simp

/-- Register-only forms: formStep logs no events and the root
leaves `events` unchanged, so the whole step's delta is the fetch delta. If every
fetch event is `derived`, the step has no data accesses, no other events, and its
derived events are exactly the fetch delta. -/
theorem register_only_delta {s s1 s' : SequentialState R c} {Δf : Array Event}
    (hfetch : Appended s s1 Δf) (hform : s'.events = s1.events)
    (hderived : ∀ e ∈ Δf.toList, projectEvent e = .derived) :
    Appended s s' Δf ∧ NoOtherEvents Δf ∧ accessesOf (deltaOf s s') = [] ∧
      derivedOf (deltaOf s s') = derivedOf Δf := by
  have happ : Appended s s' Δf := by unfold Appended at *; rw [hform, hfetch]
  have hd : deltaOf s s' = Δf := extract_of_appended happ
  refine ⟨happ, ?_, ?_, ?_⟩
  · intro e he h; rw [hderived e he] at h; cases h
  · rw [hd]; unfold accessesOf
    rw [List.filterMap_eq_nil_iff]
    intro e he; rw [hderived e he]
  · rw [hd]

end ArmCertCT.Native

#print axioms ArmCertCT.Native.EventFaithful.stepSimulation
#print axioms ArmCertCT.Native.EventFaithful.ct0_full
#print axioms ArmCertCT.Native.extract_of_appended
#print axioms ArmCertCT.Native.register_only_delta
