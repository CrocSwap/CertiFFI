-- Whole-run composition generated from signed runtime14 c01 rows.
import DefaultRuntimeC01Mem
import DefaultRuntimeC01Class
import DefaultRuntimeC01Branch

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

def capacity_c01 : Nat := 9

def past_c01 : Nat → Nat
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
  | 15 => 7
  | 16 => 7
  | 17 => 7
  | 18 => 8
  | 19 => 9
  | _ => 9

def records_c01 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 0 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 16
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 16
  | 3 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) false 4
  | 4 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (8))) false 8
  | 8 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | 10 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+mem64[x1+8]+24")) false 1
  | 14 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) true 4
  | 17 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 16
  | 18 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 16
  | _ => []

#check "CURRENT_DECL steps_c01"
theorem steps_c01 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c01) (hpath : ArmCertPipe.PathOK (extend inputs D_c01) guards_c01) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c01 regions_c01 sc base) (hp : PinsAgree p rs_c01 forms_c01 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c01.length ≤ budget) :
    ∀ k, k + 1 < plan_c01.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c01 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c01 past_c01) (records_c01 spec p k) k := by
  intro k hk
  have len : plan_c01.length = 20 := rfl
  match k, hk with
  | 0, hk => exact step_c01_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | 1, hk => exact step_c01_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | 2, hk => exact step_c01_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 3, hk => exact step_c01_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | 4, hk => exact step_c01_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | 5, hk => exact step_c01_5 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 6, hk => exact step_c01_6 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 7, hk => exact step_c01_7 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 8, hk => exact step_c01_8 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | 9, hk => exact step_c01_9 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 10, hk => exact step_c01_10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | 11, hk => exact step_c01_11 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 12, hk => exact step_c01_12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 13, hk => exact step_c01_13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 14, hk => exact step_c01_14 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | 15, hk => exact step_c01_15 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 16, hk => exact step_c01_16 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c01 past_c01 (by decide) nodup
  | 17, hk => exact step_c01_17 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | 18, hk => exact step_c01_18 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c01 past_c01 (by decide) (by decide) nodup
  | j + 19, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c01"
theorem run_c01 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c01) (hpath : ArmCertPipe.PathOK (extend inputs D_c01) guards_c01) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c01 regions_c01 sc base) (hp : PinsAgree p rs_c01 forms_c01 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c01.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c01 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c01 past_c01 0 entry) :
    (∀ k, k < plan_c01.length → ReleaseProfile.DefaultRuntime.Inv_c01 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c01 past_c01 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c01.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c01 σ0_c01 inputs plan_c01 plan_c01.length fin ∧
      fin.regs._PC = inputs.getD 83 0 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c01 spec p 19)
        (stateAt real entry (plan_c01.length - 1)) fin := by
  have len : plan_c01.length = 20 := rfl
  have chain := chain_of_evidence real entry 19 init (records_c01 spec p)
    (fun k hk => steps_c01 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c01 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c01 past_c01 nodup _ (chain.1 19 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 19 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c01"
/-- T6b DIT frame for c01: every state of the run, 0..20 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c01. -/
theorem dit_frame_c01 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c01) (hpath : ArmCertPipe.PathOK (extend inputs D_c01) guards_c01) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c01 regions_c01 sc base) (hp : PinsAgree p rs_c01 forms_c01 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c01.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c01 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c01 past_c01 0 entry) :
    ∀ k, k ≤ plan_c01.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c01.length = 20 := rfl
  have chain := chain_of_evidence real entry 19 init (records_c01 spec p)
    (fun k hk => steps_c01 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 19 init (records_c01 spec p)
    (fun k hk => steps_c01 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c01 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c01 past_c01 nodup _ (chain.1 19 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 20 with h | h
  · exact along k (by omega)
  · have e : k = 19 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 19 (by decide))

#print axioms steps_c01
#print axioms run_c01
#print axioms dit_frame_c01
end ReleaseProfile.DefaultRuntime
