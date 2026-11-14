-- Whole-run composition generated from signed runtime14 c04 rows.
import DefaultRuntimeC04Mem
import DefaultRuntimeC04Class
import DefaultRuntimeC04Branch

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

def capacity_c04 : Nat := 8

def past_c04 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | 10 => 3
  | 11 => 4
  | 12 => 4
  | 13 => 4
  | 14 => 5
  | 15 => 5
  | 16 => 5
  | 17 => 5
  | 18 => 6
  | 19 => 6
  | 20 => 7
  | 21 => 8
  | _ => 8

def records_c04 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 0 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 16
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 8
  | 5 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (8))) false 8
  | 10 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+UBFM64[1,63](x1)+24")) false 1
  | 13 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | 17 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) true 4
  | 19 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 8
  | 20 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 16
  | _ => []

#check "CURRENT_DECL steps_c04"
theorem steps_c04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c04) (hpath : ArmCertPipe.PathOK (extend inputs D_c04) guards_c04) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c04 regions_c04 sc base) (hp : PinsAgree p rs_c04 forms_c04 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c04.length ≤ budget) :
    ∀ k, k + 1 < plan_c04.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c04 past_c04) (records_c04 spec p k) k := by
  intro k hk
  have len : plan_c04.length = 22 := rfl
  match k, hk with
  | 0, hk => exact step_c04_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c04 past_c04 (by decide) (by decide) nodup
  | 1, hk => exact step_c04_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c04 past_c04 (by decide) (by decide) nodup
  | 2, hk => exact step_c04_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 3, hk => exact step_c04_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 4, hk => exact step_c04_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 5, hk => exact step_c04_5 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c04 past_c04 (by decide) (by decide) nodup
  | 6, hk => exact step_c04_6 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 7, hk => exact step_c04_7 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 8, hk => exact step_c04_8 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 9, hk => exact step_c04_9 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 10, hk => exact step_c04_10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c04 past_c04 (by decide) (by decide) nodup
  | 11, hk => exact step_c04_11 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 12, hk => exact step_c04_12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 13, hk => exact step_c04_13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c04 past_c04 (by decide) (by decide) nodup
  | 14, hk => exact step_c04_14 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 15, hk => exact step_c04_15 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 16, hk => exact step_c04_16 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 17, hk => exact step_c04_17 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c04 past_c04 (by decide) (by decide) nodup
  | 18, hk => exact step_c04_18 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c04 past_c04 (by decide) nodup
  | 19, hk => exact step_c04_19 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c04 past_c04 (by decide) (by decide) nodup
  | 20, hk => exact step_c04_20 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c04 past_c04 (by decide) (by decide) nodup
  | j + 21, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c04"
theorem run_c04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c04) (hpath : ArmCertPipe.PathOK (extend inputs D_c04) guards_c04) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c04 regions_c04 sc base) (hp : PinsAgree p rs_c04 forms_c04 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c04.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c04 past_c04 0 entry) :
    (∀ k, k < plan_c04.length → ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c04 past_c04 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c04.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c04 σ0_c04 inputs plan_c04 plan_c04.length fin ∧
      fin.regs._PC = inputs.getD 71 0 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c04 spec p 21)
        (stateAt real entry (plan_c04.length - 1)) fin := by
  have len : plan_c04.length = 22 := rfl
  have chain := chain_of_evidence real entry 21 init (records_c04 spec p)
    (fun k hk => steps_c04 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c04 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c04 past_c04 nodup _ (chain.1 21 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 21 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c04"
/-- T6b DIT frame for c04: every state of the run, 0..22 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c04. -/
theorem dit_frame_c04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c04) (hpath : ArmCertPipe.PathOK (extend inputs D_c04) guards_c04) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c04 regions_c04 sc base) (hp : PinsAgree p rs_c04 forms_c04 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c04.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c04 past_c04 0 entry) :
    ∀ k, k ≤ plan_c04.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c04.length = 22 := rfl
  have chain := chain_of_evidence real entry 21 init (records_c04 spec p)
    (fun k hk => steps_c04 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 21 init (records_c04 spec p)
    (fun k hk => steps_c04 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c04 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c04 past_c04 nodup _ (chain.1 21 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 22 with h | h
  · exact along k (by omega)
  · have e : k = 21 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 21 (by decide))

#print axioms steps_c04
#print axioms run_c04
#print axioms dit_frame_c04
end ReleaseProfile.DefaultRuntime
