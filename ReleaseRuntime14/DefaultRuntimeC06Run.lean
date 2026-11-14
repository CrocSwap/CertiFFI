-- Whole-run composition generated from signed runtime14 c06 rows.
import DefaultRuntimeC06Mem
import DefaultRuntimeC06Class
import DefaultRuntimeC06Branch

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

def capacity_c06 : Nat := 11

def past_c06 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 5
  | 8 => 5
  | 9 => 5
  | 10 => 5
  | 11 => 6
  | 12 => 7
  | 13 => 7
  | 14 => 7
  | 15 => 7
  | 16 => 7
  | 17 => 8
  | 18 => 9
  | 19 => 10
  | 20 => 11
  | _ => 11

def records_c06 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 0 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-48))) true 16
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 8
  | 2 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 16
  | 4 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) false 4
  | 5 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (8))) false 8
  | 10 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) true 4
  | 11 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | 16 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+mem64[x1+8]+24")) true 1
  | 17 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 16
  | 18 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 8
  | 19 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-48))) false 16
  | _ => []

#check "CURRENT_DECL steps_c06"
theorem steps_c06 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c06) (hpath : ArmCertPipe.PathOK (extend inputs D_c06) guards_c06) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base) (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c06.length ≤ budget) :
    ∀ k, k + 1 < plan_c06.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c06 past_c06) (records_c06 spec p k) k := by
  intro k hk
  have len : plan_c06.length = 21 := rfl
  match k, hk with
  | 0, hk => exact step_c06_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 1, hk => exact step_c06_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 2, hk => exact step_c06_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 3, hk => exact step_c06_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 4, hk => exact step_c06_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 5, hk => exact step_c06_5 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 6, hk => exact step_c06_6 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 7, hk => exact step_c06_7 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 8, hk => exact step_c06_8 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 9, hk => exact step_c06_9 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 10, hk => exact step_c06_10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 11, hk => exact step_c06_11 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 12, hk => exact step_c06_12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 13, hk => exact step_c06_13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 14, hk => exact step_c06_14 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 15, hk => exact step_c06_15 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c06 past_c06 (by decide) nodup
  | 16, hk => exact step_c06_16 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 17, hk => exact step_c06_17 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 18, hk => exact step_c06_18 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | 19, hk => exact step_c06_19 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c06 past_c06 (by decide) (by decide) nodup
  | j + 20, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c06"
theorem run_c06 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c06) (hpath : ArmCertPipe.PathOK (extend inputs D_c06) guards_c06) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base) (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c06.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c06 past_c06 0 entry) :
    (∀ k, k < plan_c06.length → ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c06 past_c06 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c06.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c06 σ0_c06 inputs plan_c06 plan_c06.length fin ∧
      fin.regs._PC = inputs.getD 99 0 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c06 spec p 20)
        (stateAt real entry (plan_c06.length - 1)) fin := by
  have len : plan_c06.length = 21 := rfl
  have chain := chain_of_evidence real entry 20 init (records_c06 spec p)
    (fun k hk => steps_c06 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c06 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c06 past_c06 nodup _ (chain.1 20 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 20 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c06"
/-- T6b DIT frame for c06: every state of the run, 0..21 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c06. -/
theorem dit_frame_c06 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c06) (hpath : ArmCertPipe.PathOK (extend inputs D_c06) guards_c06) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base) (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c06.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c06 past_c06 0 entry) :
    ∀ k, k ≤ plan_c06.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c06.length = 21 := rfl
  have chain := chain_of_evidence real entry 20 init (records_c06 spec p)
    (fun k hk => steps_c06 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 20 init (records_c06 spec p)
    (fun k hk => steps_c06 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c06 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c06 past_c06 nodup _ (chain.1 20 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 21 with h | h
  · exact along k (by omega)
  · have e : k = 20 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 20 (by decide))

#print axioms steps_c06
#print axioms run_c06
#print axioms dit_frame_c06
end ReleaseProfile.DefaultRuntime
