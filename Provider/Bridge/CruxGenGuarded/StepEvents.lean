import HeapV2StepCerts.FetchTiming
import Bridge.CruxGenGuarded.PhasedCT
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.StepEvents
open ArmBridge.Draft ArmCertWalk ArmCertCT.Native
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! (H-P3) single-run event shape of one heap-v2 step. A step from x to fin appends the
actual instruction fetch (no-update translation traffic, a pure function of (spec, PC):
Memory's fetch_records) then the ifetch read, then the step's data events D (empty for
class/branch/BL/RET steps: their actions, PMU and post phases are event-silent; memory steps
supply D's frozen records). Every rich step's R carries `EvShape`, so two runs with
equal PC and equal data records append record-equal deltas (`pair`). -/

/-- The ifetch read at PC with PA n. -/
def ifetchEv (n : Nat) (pc : BitVec 64) : Event := .memRead n 4 (some pc.toNat) (AK_ifetch ()) false

/-- Step x → fin appends exactly fetch traffic + ifetch + D, D having records `data`. -/
def EvShape {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (x fin : NativeState) : Prop :=
  ∃ (n : Nat) (T D : Array Event),
    fin.events = x.events ++ T ++ #[ifetchEv n x.regs._PC] ++ D ∧
    T.toList.map V2.trafficRec = trafficRecsOf spec x.regs._PC ∧
    mapping x.regs._PC = some n ∧
    D.toList.map ArmCertCTOrdered.OrderedEventV2.record = data

/-- Traffic events keep their V2 traffic record under the frozen record. -/
theorem record_of_traffic {e : Event} {v : V2.TrafficRec} (h : V2.trafficRec e = some v) :
    ArmCertCTOrdered.OrderedEventV2.record e = some (.traffic v) := by
  unfold ArmCertCTOrdered.OrderedEventV2.record
  split
  · simp [V2.trafficRec] at h
  · rw [h]

theorem records_of_traffic (T : List Event) (vs : List (Option V2.TrafficRec))
    (h : T.map V2.trafficRec = vs) (some_ : ∀ v ∈ vs, v.isSome = true) :
    T.map ArmCertCTOrdered.OrderedEventV2.record = vs.map (Option.map .traffic) := by
  subst h
  induction T with
  | nil => rfl
  | cons e T ih =>
    simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at some_ ⊢
    obtain ⟨he, hT⟩ := some_
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp he
    rw [record_of_traffic hv, hv, ih hT]
    rfl

theorem trafficRecsOf_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) :
    ∀ v ∈ trafficRecsOf spec va, v.isSome = true := by
  intro v hv
  simp only [trafficRecsOf, List.mem_cons, List.mem_append, List.mem_map, List.mem_singleton] at hv
  rcases hv with rfl | ⟨_, _, rfl⟩ | rfl | h <;> first | rfl | (simp at h)

run_cmd do
  IO.eprintln "CURRENT_DECL StepEvents.pair"
  (← IO.getStderr).flush

/-- Pairing: two steps with event shapes at equal PC (same deployment) and equal data
records, landing on equal PCs, are -timing-equal. -/
theorem pair {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (l r lf rf : NativeState)
    (hl : EvShape spec mapping data l lf) (hr : EvShape spec mapping data r rf)
    (pc : l.regs._PC = r.regs._PC) (pcf : lf.regs._PC = rf.regs._PC) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record l r lf rf := by
  obtain ⟨nl, Tl, Dl, el, tl, ml, dl⟩ := hl
  obtain ⟨nr, Tr, Dr, er, tr, mr, dr⟩ := hr
  have nn : nl = nr := by rw [pc] at ml; rw [ml] at mr; exact Option.some.inj mr
  refine ⟨⟨Tl ++ #[ifetchEv nl l.regs._PC] ++ Dl, Tr ++ #[ifetchEv nr r.regs._PC] ++ Dr, ?_, ?_, ?_⟩, pcf⟩
  · rw [el]; simp only [Array.append_assoc]
  · rw [er]; simp only [Array.append_assoc]
  · have tl' := records_of_traffic Tl.toList _ tl (trafficRecsOf_some spec _)
    have tr' := records_of_traffic Tr.toList _ tr (trafficRecsOf_some spec _)
    simp only [Array.toList_append, List.map_append, tl', tr', dl, dr, pc, nn]

#print axioms record_of_traffic
#print axioms pair
end ArmBridge.CruxGenGuarded.StepEvents
