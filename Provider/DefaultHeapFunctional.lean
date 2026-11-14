-- Functional output from every actual current-profile value step.
import DefaultHeapValueRun
import DefaultHeapBody
import ArmCertValue.Functional
import ArmCertValueMem.Coherent
import TranslateMem.WalkE17
import HeapV2StepCerts.ScrubBind

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCertValue ArmCertValue.HeapV2Plan
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapRun

theorem input_present {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {pins : HeapV2E17.Pins} {entry : NativeState} {budget : Nat}
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) :
    ∀ j, j < 32 → ∃ b, Release.bufByte mapping entry pins.x1 j = some b := by
  intro j hj
  obtain ⟨e, he, hc⟩ :=
    List.any_eq_true.1 (List.all_eq_true.1 TranslateMem.input_accesses j (List.mem_range.2 hj))
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hpin, hoff⟩, hsz⟩ := hc
  have hva : HeapV2E17.dataVA pins e = BitVec.ofNat 64 (pins.x1 + j) := by
    obtain ⟨k, pn, off, size, w⟩ := e
    simp only at hpin hoff
    subst hpin hoff
    apply BitVec.eq_of_toNat_eq
    simp [HeapV2E17.dataVA, HeapV2E17.pin, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  obtain ⟨pa, facts⟩ := C3.data_facts dp.dataStatic he
  have mapped := facts.mapped
  rw [hva] at mapped
  have pres := dp.init.present e he pa.toNat facts.mapped 0 (by omega)
  rw [Nat.add_zero] at pres
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 pres
  exact ⟨b, by show (mapping _).bind _ = _; rw [mapped]; simpa using hb⟩

#check "CURRENT_DECL heap body_functional"
theorem body_functional (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget)
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping) :
    Release.Functional mapping pins entry (stateAt real entry 357) := by
  have hpres := input_present catalogue capacity drawsBefore dp
  let bytes : Nat → BitVec 8 := fun j => (Release.bufByte mapping entry pins.x1 j).getD 0#8
  have hσ : ∀ j, j < 32 → Release.bufByte mapping entry pins.x1 j = some (bytes j) := by
    intro j hj
    obtain ⟨b, h⟩ := hpres j hj
    simp only [bytes, h, Option.getD_some]
  have hI : ∀ j, j < 32 →
      regionByte mapping (HeapV2E17.pin pins) entry I j = some (bytes j) := by
    intro j hj
    rw [show I = (⟨2, 0, 4⟩ : Region) from rfl, regionByte_eq_bufByte]
    exact hσ j hj
  have hinv : ∀ k, k < plan.length →
      RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore (stateAt real entry k) := by
    intro k hk
    rw [plan_length] at hk
    exact prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k (by omega)
  have hplan := planHolds_of_steps real ((fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore))
    mapping (HeapV2E17.pin pins) regions plan entry hinv
    (value_steps real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj)
  have hout := hp1_run mapping (HeapV2E17.pin pins) (stateAt real entry) (mkInputs entry bytes)
    (mkInputs_length _ _) (mkInputs_bytes _ _) (ArmCertValue.MemRegion.regionCoherent mapping _)
    (agrees_σ0 mapping (HeapV2E17.pin pins) entry bytes hI) hplan
  have hval := inVal_mkInputs mapping pins entry entry bytes hσ
  have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb 357 (by decide)
  have hx0 : (stateAt real entry 357).regs.gpr[0] = 0#64 := by
    simpa [RegBind.regVal, Fin.castLE] using ValBind.scrub_at_357 inv.1.valBind ⟨0, by decide⟩
  refine ⟨hx0, ?_⟩
  intro i hi
  rw [← show HeapV2E17.pin pins 1 = pins.x0 from rfl,
      ← regionByte_eq_bufByte mapping (HeapV2E17.pin pins) _ 1 4 i]
  rw [show (⟨1, 0, 4⟩ : Region) = O from rfl, hout i hi, hval, p256k1_eq]

#check "CURRENT_DECL heap body_functional_return"
theorem body_functional_return (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping)
    (low : entry.regs.gpr[30].toNat < 2 ^ 55) :
    Release.Functional mapping pins entry (stateAt real entry 358) := by
  obtain ⟨x0, output⟩ := body_functional real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp (by omega) dbl inj
  obtain ⟨fin, run, _, gpr, _, mem, _, _, _⟩ := body_ret real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb low
  rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
  refine ⟨by rw [gpr]; exact x0, ?_⟩
  intro i hi
  simpa only [Release.bufByte, mem] using output i hi

#check "CURRENT_DECL heap shim_functional"
theorem shim_functional (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins (stateAt real entry 7) budget catalogue capacity drawsBefore)
    (hb : 357 ≤ budget)
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping)
    (inputFrame : ∀ i, i < 32 → Release.bufByte mapping (stateAt real entry 7) pins.x1 i =
      Release.bufByte mapping entry pins.x1 i)
    (outputFrame : ∀ i, i < 32 → Release.bufByte mapping (stateAt real entry 369) pins.x0 i =
      Release.bufByte mapping (stateAt real entry 364) pins.x0 i)
    (x0Frame : (stateAt real entry 369).regs.gpr[0] = (stateAt real entry 364).regs.gpr[0]) :
    Release.Functional mapping pins entry (stateAt real entry 369) := by
  let bodyEntry := stateAt real entry 7
  let bytes : Nat → BitVec 8 := fun i => (Release.bufByte mapping entry pins.x1 i).getD 0#8
  have present := input_present catalogue capacity drawsBefore dp
  have bodyBytes : ∀ i, i < 32 →
      Release.bufByte mapping bodyEntry pins.x1 i = some (bytes i) := by
    intro i hi
    obtain ⟨b, h⟩ := present i hi
    have he := (inputFrame i hi).symm.trans h
    simp only [bytes, he, Option.getD_some]
    exact h
  have entryBytes : ∀ i, i < 32 → Release.bufByte mapping entry pins.x1 i = some (bytes i) := by
    intro i hi
    rw [← inputFrame i hi]
    exact bodyBytes i hi
  have hI : ∀ i, i < 32 →
      regionByte mapping (HeapV2E17.pin pins) bodyEntry I i = some (bytes i) := by
    intro i hi
    rw [show I = (⟨2, 0, 4⟩ : Region) from rfl, regionByte_eq_bufByte]
    exact bodyBytes i hi
  have hinv : ∀ k, k < plan.length →
      RunInv spec config rows mapping base pins bodyEntry budget k catalogue capacity drawsBefore (stateAt real bodyEntry k) := by
    intro k hk
    rw [plan_length] at hk
    exact prefixes real spec config rows mapping base pins bodyEntry budget catalogue capacity drawsBefore dp hb k (by omega)
  have inv := prefixes real spec config rows mapping base pins bodyEntry budget catalogue capacity drawsBefore dp hb 357 (by decide)
  have zero : (stateAt real entry 364).regs.gpr[0] = 0#64 := by
    rw [show (364 : Nat) = 7 + 357 from rfl, Release.body_index]
    simpa [bodyEntry, RegBind.regVal, Fin.castLE] using ValBind.scrub_at_357 inv.1.valBind ⟨0, by decide⟩
  exact functional_of_value real mapping pins entry
    ((fun k => RunInv spec config rows mapping base pins bodyEntry budget k catalogue capacity drawsBefore)) rfl
    (ArmCertValue.MemRegion.regionCoherent mapping _) hinv
    (value_steps real spec config rows mapping base pins bodyEntry budget catalogue capacity drawsBefore dp hb dbl inj)
    bytes hI entryBytes outputFrame (x0Frame.trans zero)

#print axioms input_present
#print axioms body_functional
#print axioms body_functional_return
#print axioms shim_functional
end ReleaseProfile.DefaultHeapRun
