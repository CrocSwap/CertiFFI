-- Whole-run composition generated from signed runtime14 c03 rows.
import DefaultRuntimeC03Mem
import DefaultRuntimeC03Class
import DefaultRuntimeC03Branch

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

def capacity_c03 : Nat := 8

def past_c03 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | 6 => 4
  | 7 => 4
  | 8 => 4
  | 9 => 5
  | 10 => 5
  | 11 => 6
  | 12 => 6
  | 13 => 6
  | 14 => 6
  | 15 => 6
  | 16 => 6
  | 17 => 7
  | 18 => 8
  | _ => 8

def records_c03 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 0 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 16
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 16
  | 3 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) false 4
  | 4 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (8))) false 8
  | 8 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | 10 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+mem64[x1+8]+24")) false 1
  | 16 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 16
  | 17 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 16
  | _ => []

#check "CURRENT_DECL steps_c03"
theorem steps_c03 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c03) (hpath : ArmCertPipe.PathOK (extend inputs D_c03) guards_c03) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c03 regions_c03 sc base) (hp : PinsAgree p rs_c03 forms_c03 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c03.length ≤ budget) :
    ∀ k, k + 1 < plan_c03.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c03 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c03 past_c03) (records_c03 spec p k) k := by
  intro k hk
  have len : plan_c03.length = 19 := rfl
  match k, hk with
  | 0, hk => exact step_c03_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c03 past_c03 (by decide) (by decide) nodup
  | 1, hk => exact step_c03_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c03 past_c03 (by decide) (by decide) nodup
  | 2, hk => exact step_c03_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 3, hk => exact step_c03_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c03 past_c03 (by decide) (by decide) nodup
  | 4, hk => exact step_c03_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c03 past_c03 (by decide) (by decide) nodup
  | 5, hk => exact step_c03_5 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 6, hk => exact step_c03_6 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 7, hk => exact step_c03_7 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 8, hk => exact step_c03_8 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c03 past_c03 (by decide) (by decide) nodup
  | 9, hk => exact step_c03_9 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 10, hk => exact step_c03_10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c03 past_c03 (by decide) (by decide) nodup
  | 11, hk => exact step_c03_11 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 12, hk => exact step_c03_12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 13, hk => exact step_c03_13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 14, hk => exact step_c03_14 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 15, hk => exact step_c03_15 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c03 past_c03 (by decide) nodup
  | 16, hk => exact step_c03_16 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c03 past_c03 (by decide) (by decide) nodup
  | 17, hk => exact step_c03_17 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c03 past_c03 (by decide) (by decide) nodup
  | j + 18, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c03"
theorem run_c03 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c03) (hpath : ArmCertPipe.PathOK (extend inputs D_c03) guards_c03) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c03 regions_c03 sc base) (hp : PinsAgree p rs_c03 forms_c03 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c03.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c03 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c03 past_c03 0 entry) :
    (∀ k, k < plan_c03.length → ReleaseProfile.DefaultRuntime.Inv_c03 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c03 past_c03 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c03.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c03 σ0_c03 inputs plan_c03 plan_c03.length fin ∧
      fin.regs._PC = inputs.getD 83 0 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c03 spec p 18)
        (stateAt real entry (plan_c03.length - 1)) fin := by
  have len : plan_c03.length = 19 := rfl
  have chain := chain_of_evidence real entry 18 init (records_c03 spec p)
    (fun k hk => steps_c03 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c03 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c03 past_c03 nodup _ (chain.1 18 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 18 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c03"
/-- T6b DIT frame for c03: every state of the run, 0..19 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c03. -/
theorem dit_frame_c03 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c03) (hpath : ArmCertPipe.PathOK (extend inputs D_c03) guards_c03) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c03 regions_c03 sc base) (hp : PinsAgree p rs_c03 forms_c03 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c03.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c03 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c03 past_c03 0 entry) :
    ∀ k, k ≤ plan_c03.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c03.length = 19 := rfl
  have chain := chain_of_evidence real entry 18 init (records_c03 spec p)
    (fun k hk => steps_c03 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 18 init (records_c03 spec p)
    (fun k hk => steps_c03 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c03 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c03 past_c03 nodup _ (chain.1 18 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 19 with h | h
  · exact along k (by omega)
  · have e : k = 18 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 18 (by decide))

#print axioms steps_c03
#print axioms run_c03
#print axioms dit_frame_c03
end ReleaseProfile.DefaultRuntime
