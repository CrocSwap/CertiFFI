-- Whole-run composition generated from signed runtime14 c07 rows.
import DefaultRuntimeC07Mem
import DefaultRuntimeC07Class
import DefaultRuntimeC07Branch

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

def capacity_c07 : Nat := 10

def past_c07 : Nat → Nat
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
  | 12 => 6
  | 13 => 6
  | 14 => 6
  | 15 => 6
  | 16 => 7
  | 17 => 8
  | 18 => 9
  | 19 => 10
  | _ => 10

def records_c07 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 0 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-48))) true 16
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 8
  | 2 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 16
  | 4 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) false 4
  | 5 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (8))) false 8
  | 10 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | 15 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+mem64[x1+8]+24")) true 1
  | 16 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 16
  | 17 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 8
  | 18 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-48))) false 16
  | _ => []

#check "CURRENT_DECL steps_c07"
theorem steps_c07 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c07) (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 sc base) (hp : PinsAgree p rs_c07 forms_c07 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c07.length ≤ budget) :
    ∀ k, k + 1 < plan_c07.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c07 past_c07) (records_c07 spec p k) k := by
  intro k hk
  have len : plan_c07.length = 20 := rfl
  match k, hk with
  | 0, hk => exact step_c07_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 1, hk => exact step_c07_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 2, hk => exact step_c07_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 3, hk => exact step_c07_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 4, hk => exact step_c07_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 5, hk => exact step_c07_5 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 6, hk => exact step_c07_6 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 7, hk => exact step_c07_7 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 8, hk => exact step_c07_8 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 9, hk => exact step_c07_9 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 10, hk => exact step_c07_10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 11, hk => exact step_c07_11 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 12, hk => exact step_c07_12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 13, hk => exact step_c07_13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 14, hk => exact step_c07_14 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c07 past_c07 (by decide) nodup
  | 15, hk => exact step_c07_15 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 16, hk => exact step_c07_16 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 17, hk => exact step_c07_17 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | 18, hk => exact step_c07_18 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c07 past_c07 (by decide) (by decide) nodup
  | j + 19, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c07"
theorem run_c07 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c07) (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 sc base) (hp : PinsAgree p rs_c07 forms_c07 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c07.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c07 past_c07 0 entry) :
    (∀ k, k < plan_c07.length → ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c07 past_c07 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c07.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c07 σ0_c07 inputs plan_c07 plan_c07.length fin ∧
      fin.regs._PC = inputs.getD 99 0 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c07 spec p 19)
        (stateAt real entry (plan_c07.length - 1)) fin := by
  have len : plan_c07.length = 20 := rfl
  have chain := chain_of_evidence real entry 19 init (records_c07 spec p)
    (fun k hk => steps_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c07 past_c07 nodup _ (chain.1 19 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 19 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c07"
/-- T6b DIT frame for c07: every state of the run, 0..20 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c07. -/
theorem dit_frame_c07 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c07) (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 sc base) (hp : PinsAgree p rs_c07 forms_c07 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c07.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c07 past_c07 0 entry) :
    ∀ k, k ≤ plan_c07.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c07.length = 20 := rfl
  have chain := chain_of_evidence real entry 19 init (records_c07 spec p)
    (fun k hk => steps_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 19 init (records_c07 spec p)
    (fun k hk => steps_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c07 past_c07 nodup _ (chain.1 19 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 20 with h | h
  · exact along k (by omega)
  · have e : k = 19 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 19 (by decide))

#print axioms steps_c07
#print axioms run_c07
#print axioms dit_frame_c07
end ReleaseProfile.DefaultRuntime
