-- Whole-run composition generated from signed runtime14 c12 rows.
import DefaultRuntimeC12Mem
import DefaultRuntimeC12Class
import DefaultRuntimeC12Branch

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

def capacity_c12 : Nat := 2

def past_c12 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | _ => 2

def records_c12 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 19 (0))) false 4
  | 5 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 19 (0))) true 4
  | _ => []

#check "CURRENT_DECL steps_c12"
theorem steps_c12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c12) (hpath : ArmCertPipe.PathOK (extend inputs D_c12) guards_c12)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c12 regions_c12 sc base) (hp : PinsAgree p rs_c12 forms_c12 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c12.length ≤ budget) :
    ∀ k, k + 1 < plan_c12.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c12 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c12 past_c12) (records_c12 spec p k) k := by
  intro k hk
  have len : plan_c12.length = 6 := rfl
  match k, hk with
  | 0, hk => exact step_c12_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c12 past_c12 (by decide) nodup
  | 1, hk => exact step_c12_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c12 past_c12 (by decide) (by decide) nodup
  | 2, hk => exact step_c12_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c12 past_c12 (by decide) nodup
  | 3, hk => exact step_c12_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c12 past_c12 (by decide) nodup
  | 4, hk => exact step_c12_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c12 past_c12 (by decide) nodup
  | j + 5, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c12"
theorem run_c12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c12) (hpath : ArmCertPipe.PathOK (extend inputs D_c12) guards_c12)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c12 regions_c12 sc base) (hp : PinsAgree p rs_c12 forms_c12 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c12.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c12 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c12 past_c12 0 entry) :
    (∀ k, k < plan_c12.length → ReleaseProfile.DefaultRuntime.Inv_c12 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c12 past_c12 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c12.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c12 σ0_c12 inputs plan_c12 plan_c12.length fin ∧
      fin.regs._PC = base + (offset_c12 5 + 4#64) ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c12 spec p 5)
        (stateAt real entry (plan_c12.length - 1)) fin := by
  have len : plan_c12.length = 6 := rfl
  have chain := chain_of_evidence real entry 5 init (records_c12 spec p)
    (fun k hk => steps_c12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c12 past_c12 (by decide) nodup _ (chain.1 5 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 5 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c12"
/-- T6b DIT frame for c12: every state of the run, 0..6 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c12. -/
theorem dit_frame_c12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c12) (hpath : ArmCertPipe.PathOK (extend inputs D_c12) guards_c12)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c12 regions_c12 sc base) (hp : PinsAgree p rs_c12 forms_c12 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c12.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c12 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c12 past_c12 0 entry) :
    ∀ k, k ≤ plan_c12.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c12.length = 6 := rfl
  have chain := chain_of_evidence real entry 5 init (records_c12 spec p)
    (fun k hk => steps_c12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 5 init (records_c12 spec p)
    (fun k hk => steps_c12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c12 past_c12 (by decide) nodup _ (chain.1 5 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 6 with h | h
  · exact along k (by omega)
  · have e : k = 5 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 5 (by decide))

#print axioms steps_c12
#print axioms run_c12
#print axioms dit_frame_c12
end ReleaseProfile.DefaultRuntime
