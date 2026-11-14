-- (, H-P3): EvShape from a step's fetch run. A rich step's R carries
-- `∃ f w, __FetchInstr (beforeFetchState x).PC (beforeFetchState x) = .ok (A64, w) f ∧ fin.events = f.events`
-- (rich-v4); with fetch_records at beforeFetchState x and determinism of the fetch, that is
-- EvShape spec mapping [] x fin. Generic in the step kind (D = [] for every non-memory step).
import Bridge.CruxGenGuarded.StepEvents
import Bridge.CruxGenGuarded.ChainInvV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace RtB4.EvShapeBridge

theorem evShape_of_fetchRun {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (x fin : NativeState) (stepPins : StepPins x) (features : EntryFeatures x.regs)
    (debug : E11Debug.E11CheckDebug x.regs)
    (current : CurrentS1At spec config rows (beforeFetchState x))
    (pcLow : Sail.BitVec.extractLsb x.regs._PC 1 0 = 0#2)
    (ob : FetchObligations spec config rows mapping w x)
    (raw : RawImageAt spec.imageRows x.mem)
    (noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (fetchRun : ∃ f w', __FetchInstr (beforeFetchState x).regs._PC (beforeFetchState x) =
      .ok (__InstrEnc.__A64, w') f ∧ fin.events = f.events) :
    StepEvents.EvShape spec mapping [] x fin := by
  have pins := NativeEntryTail.EntryPins.of_scalar x stepPins
  obtain ⟨step, el, il, _pc, _emu0, e11, mode, spe⟩ := before_fetch_facts x pins features debug
  obtain ⟨_acc, word, final, n, T, _address, _faultOut, _translated, _data, _actual, frun, mapped, fev, ftr,
      -⟩ :=
    HeapV2StepCerts.FetchTiming.fetch_records spec config rows mapping (beforeFetchState x) step el pcLow il
      current mode step.b0 ⟨e11.mde, e11.hde⟩ spe ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc
      raw noUpd nodup
  obtain ⟨f, w', run, evs⟩ := fetchRun
  rw [frun] at run
  have same : final = f := by
    injection run with h1 h2
  subst same
  refine ⟨n, T, #[], ?_, ftr, mapped, rfl⟩
  rw [evs, fev]
  rfl

#print axioms evShape_of_fetchRun
end RtB4.EvShapeBridge
