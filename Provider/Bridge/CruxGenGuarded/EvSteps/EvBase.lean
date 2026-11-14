import Bridge.CruxGenGuarded.EvClass
import HeapV2StepCerts.E17General.Base
import HeapV2StepCerts.DataRecs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace ArmBridge.CruxGenGuarded.EvSteps
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! per-step data records: the plan's data access of step k (Memory's DataRecs), [] otherwise. -/
def dataOf {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins) (k : Nat) :
    List (Option ArmCertCTOrdered.OrderedEventV2.Record) :=
  match HeapV2Plan.symbolicAccesses.find? (·.1 = k) with
  | some e => HeapV2StepCerts.DataRecs.dataRecs spec (HeapV2E17.dataVA pins e) e.2.2.2.2 e.2.2.2.1
  | none => []

/-- The event-shape step family over e17_general's deployment. -/
def EvStep (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget k : Nat) : Prop :=
  ∀ x, I4 spec config rows mapping base pins entry budget k x →
    ∃ fin, modelStep real x = .ok () fin ∧ StepEvents.EvShape spec mapping (dataOf spec pins k) x fin
end ArmBridge.CruxGenGuarded.EvSteps
