-- Whole-run composition generated from signed runtime14 c10 rows.
import DefaultRuntimeC10Mem
import DefaultRuntimeC10Class
import DefaultRuntimeC10Branch

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultRuntime
open PipeR14 PipeR14.Physical

def capacity_c10 : Nat := 1

def past_c10 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 1

def records_c10 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | _ => []

#check "CURRENT_DECL steps_c10"
theorem steps_c10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c10) (hpath : ArmCertPipe.PathOK (extend inputs D_c10) guards_c10)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c10 regions_c10 sc base) (hp : PinsAgree p rs_c10 forms_c10 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c10.length ≤ budget) :
    ∀ k, k + 1 < plan_c10.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c10 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c10 past_c10) (records_c10 spec p k) k := by
  intro k hk
  have len : plan_c10.length = 7 := rfl
  match k, hk with
  | 0, hk => exact step_c10_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c10 past_c10 (by decide) nodup
  | 1, hk => exact step_c10_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c10 past_c10 (by decide) (by decide) nodup
  | 2, hk => exact step_c10_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c10 past_c10 (by decide) nodup
  | 3, hk => exact step_c10_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c10 past_c10 (by decide) nodup
  | 4, hk => exact step_c10_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c10 past_c10 (by decide) nodup
  | 5, hk => exact step_c10_5 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c10 past_c10 (by decide) nodup
  | j + 6, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c10"
theorem run_c10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c10) (hpath : ArmCertPipe.PathOK (extend inputs D_c10) guards_c10)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c10 regions_c10 sc base) (hp : PinsAgree p rs_c10 forms_c10 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c10.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c10 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c10 past_c10 0 entry) :
    (∀ k, k < plan_c10.length → ReleaseProfile.DefaultRuntime.Inv_c10 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c10 past_c10 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c10.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c10 σ0_c10 inputs plan_c10 plan_c10.length fin ∧
      fin.regs._PC = base + BitVec.ofNat 64 0x2baa78 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c10 spec p 6)
        (stateAt real entry (plan_c10.length - 1)) fin := by
  have len : plan_c10.length = 7 := rfl
  have chain := chain_of_evidence real entry 6 init (records_c10 spec p)
    (fun k hk => steps_c10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c10 past_c10 nodup _ (chain.1 6 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 6 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c10"
/-- T6b DIT frame for c10: every state of the run, 0..7 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c10. -/
theorem dit_frame_c10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c10) (hpath : ArmCertPipe.PathOK (extend inputs D_c10) guards_c10)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c10 regions_c10 sc base) (hp : PinsAgree p rs_c10 forms_c10 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c10.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c10 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c10 past_c10 0 entry) :
    ∀ k, k ≤ plan_c10.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c10.length = 7 := rfl
  have chain := chain_of_evidence real entry 6 init (records_c10 spec p)
    (fun k hk => steps_c10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 6 init (records_c10 spec p)
    (fun k hk => steps_c10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c10 past_c10 nodup _ (chain.1 6 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 7 with h | h
  · exact along k (by omega)
  · have e : k = 6 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 6 (by decide))

#print axioms steps_c10
#print axioms run_c10
#print axioms dit_frame_c10
end ReleaseProfile.DefaultRuntime
