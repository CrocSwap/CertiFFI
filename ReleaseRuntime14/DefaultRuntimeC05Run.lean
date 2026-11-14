-- Whole-run composition generated from signed runtime14 c05 rows.
import DefaultRuntimeC05Mem
import DefaultRuntimeC05Class
import DefaultRuntimeC05Branch

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

def capacity_c05 : Nat := 7

def past_c05 : Nat → Nat
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
  | 18 => 5
  | 19 => 6
  | 20 => 7
  | _ => 7

def records_c05 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 0 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 16
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 8
  | 5 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (8))) false 8
  | 10 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+UBFM64[1,63](x1)+24")) false 1
  | 13 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | 18 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 8
  | 19 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 16
  | _ => []

#check "CURRENT_DECL steps_c05"
theorem steps_c05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c05) (hpath : ArmCertPipe.PathOK (extend inputs D_c05) guards_c05) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base) (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c05.length ≤ budget) :
    ∀ k, k + 1 < plan_c05.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c05 past_c05) (records_c05 spec p k) k := by
  intro k hk
  have len : plan_c05.length = 21 := rfl
  match k, hk with
  | 0, hk => exact step_c05_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c05 past_c05 (by decide) (by decide) nodup
  | 1, hk => exact step_c05_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c05 past_c05 (by decide) (by decide) nodup
  | 2, hk => exact step_c05_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 3, hk => exact step_c05_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 4, hk => exact step_c05_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 5, hk => exact step_c05_5 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c05 past_c05 (by decide) (by decide) nodup
  | 6, hk => exact step_c05_6 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 7, hk => exact step_c05_7 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 8, hk => exact step_c05_8 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 9, hk => exact step_c05_9 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 10, hk => exact step_c05_10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c05 past_c05 (by decide) (by decide) nodup
  | 11, hk => exact step_c05_11 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 12, hk => exact step_c05_12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 13, hk => exact step_c05_13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c05 past_c05 (by decide) (by decide) nodup
  | 14, hk => exact step_c05_14 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 15, hk => exact step_c05_15 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 16, hk => exact step_c05_16 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 17, hk => exact step_c05_17 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c05 past_c05 (by decide) nodup
  | 18, hk => exact step_c05_18 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c05 past_c05 (by decide) (by decide) nodup
  | 19, hk => exact step_c05_19 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c05 past_c05 (by decide) (by decide) nodup
  | j + 20, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c05"
theorem run_c05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c05) (hpath : ArmCertPipe.PathOK (extend inputs D_c05) guards_c05) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base) (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c05.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c05 past_c05 0 entry) :
    (∀ k, k < plan_c05.length → ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c05 past_c05 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c05.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c05 σ0_c05 inputs plan_c05 plan_c05.length fin ∧
      fin.regs._PC = inputs.getD 71 0 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c05 spec p 20)
        (stateAt real entry (plan_c05.length - 1)) fin := by
  have len : plan_c05.length = 21 := rfl
  have chain := chain_of_evidence real entry 20 init (records_c05 spec p)
    (fun k hk => steps_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c05 past_c05 nodup _ (chain.1 20 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 20 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c05"
/-- T6b DIT frame for c05: every state of the run, 0..21 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c05. -/
theorem dit_frame_c05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c05) (hpath : ArmCertPipe.PathOK (extend inputs D_c05) guards_c05) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base) (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c05.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c05 past_c05 0 entry) :
    ∀ k, k ≤ plan_c05.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c05.length = 21 := rfl
  have chain := chain_of_evidence real entry 20 init (records_c05 spec p)
    (fun k hk => steps_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 20 init (records_c05 spec p)
    (fun k hk => steps_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hlr catalogue entry capacity_c05 past_c05 nodup _ (chain.1 20 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 21 with h | h
  · exact along k (by omega)
  · have e : k = 20 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 20 (by decide))

#print axioms steps_c05
#print axioms run_c05
#print axioms dit_frame_c05
end ReleaseProfile.DefaultRuntime
