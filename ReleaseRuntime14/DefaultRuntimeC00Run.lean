-- All c00 physical steps and the terminal RET under the current profile.
import DefaultRuntimeC00Mem
import DefaultRuntimeC00Class
import DefaultRuntimeC00Branch

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

def capacity_c00 : Nat := 10

def past_c00 : Nat → Nat
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
  | 10 => 6
  | 11 => 6
  | 12 => 7
  | 13 => 7
  | 14 => 7
  | 15 => 7
  | 16 => 8
  | 17 => 8
  | 18 => 8
  | 19 => 9
  | 20 => 10
  | _ => 10

def records_c00 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 0 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 16
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 16
  | 3 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) false 4
  | 4 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (8))) false 8
  | 8 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) true 4
  | 9 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | 11 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+mem64[x1+8]+24")) false 1
  | 15 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) true 4
  | 18 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 16
  | 19 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 16
  | _ => []

#check "CURRENT_DECL steps_c00"
theorem steps_c00 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c00) (hpath : ArmCertPipe.PathOK (extend inputs D_c00) guards_c00) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c00 regions_c00 sc base) (hp : PinsAgree p rs_c00 forms_c00 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c00.length ≤ budget) :
    ∀ k, k + 1 < plan_c00.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
        table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c00 past_c00) (records_c00 spec p k) k := by
  intro k hk
  have len : plan_c00.length = 21 := rfl
  match k, hk with
  | 0, hk => exact step_c00_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 1, hk => exact step_c00_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 2, hk => exact step_c00_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 3, hk => exact step_c00_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 4, hk => exact step_c00_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 5, hk => exact step_c00_5 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 6, hk => exact step_c00_6 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 7, hk => exact step_c00_7 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 8, hk => exact step_c00_8 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 9, hk => exact step_c00_9 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 10, hk => exact step_c00_10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 11, hk => exact step_c00_11 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 12, hk => exact step_c00_12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 13, hk => exact step_c00_13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 14, hk => exact step_c00_14 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 15, hk => exact step_c00_15 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 16, hk => exact step_c00_16 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 17, hk => exact step_c00_17 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c00 past_c00 (by decide) nodup
  | 18, hk => exact step_c00_18 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | 19, hk => exact step_c00_19 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c00 past_c00 (by decide) (by decide) nodup
  | j + 20, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c00"
theorem run_c00 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c00) (hpath : ArmCertPipe.PathOK (extend inputs D_c00) guards_c00) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c00 regions_c00 sc base) (hp : PinsAgree p rs_c00 forms_c00 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c00.length ≤ budget)
    (entry : NativeState)
    (init : ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c00 past_c00 0 entry) :
    (∀ k, k < plan_c00.length → ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c00 past_c00 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c00.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c00 σ0_c00 inputs plan_c00 plan_c00.length fin ∧
      fin.regs._PC = inputs.getD 83 0 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping [] (stateAt real entry (plan_c00.length - 1)) fin := by
  have len : plan_c00.length = 21 := rfl
  have chain := chain_of_evidence real entry 20 init (records_c00 spec p)
    (fun k hk => steps_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c00 past_c00 nodup _ (chain.1 20 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 20 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c00"
/-- T6b DIT frame for c00: every state of the run, 0..21 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c00. -/
theorem dit_frame_c00 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c00) (hpath : ArmCertPipe.PathOK (extend inputs D_c00) guards_c00) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c00 regions_c00 sc base) (hp : PinsAgree p rs_c00 forms_c00 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c00.length ≤ budget)
    (entry : NativeState)
    (init : ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c00 past_c00 0 entry) :
    ∀ k, k ≤ plan_c00.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c00.length = 21 := rfl
  have chain := chain_of_evidence real entry 20 init (records_c00 spec p)
    (fun k hk => steps_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 20 init (records_c00 spec p)
    (fun k hk => steps_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c00 past_c00 nodup _ (chain.1 20 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 21 with h | h
  · exact along k (by omega)
  · have e : k = 20 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 20 (by decide))

#print axioms steps_c00
#print axioms run_c00
#print axioms dit_frame_c00
end ReleaseProfile.DefaultRuntime
