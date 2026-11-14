import PipeLean_D234_SecpSqrAlt_c27.DitBodyState
import DitShim243.RawFetch
import PipeLean_D234_SecpSqrAlt_c27.DefaultState
import ArmCertValueTail.Adc64
import ArmCertValueTail.Adc64ZRm
import ArmCertValueTail.Adcs64
import ArmCertValueTail.Adcs64ZRm
import ArmCertValueTail.AddImm64
import ArmCertValueTail.AddsShift64
import ArmCertValueTail.Csel3
import ArmCertValueTail.Csinc3
import ArmCertValueTail.Madd64
import ArmCertValueTail.Movz64z
import ArmCertValueTail.OrrImm32_0
import ArmCertValueTail.Sbc64
import ArmCertValueTail.Sbcs64
import ArmCertValueTail.SubsShift64
import ArmCertValueTail.Umulh64
import TranslateScalarTagCheck.Tails
import TranslateSpan.DefaultScalar
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSqrAlt_c27.DitBodyScalar

theorem site_1 : EntryBinding.plan.code[1]? = some (7596, 2600696905) := rfl
theorem room_1 (initial : NativeState) : 1 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_1 : NativeEntryBodyDispatch.Madd64.selected 9#5 2#5 3#5 = 2600696905#32 := by decide
theorem step_1 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (1+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[1]'(room_1 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7596, 2600696905) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_1
  have pc : x.regs._PC = MemReloc.imageAddress base 7596 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (7596, 2600696905) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (1+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 1 + 4#64 = offset EntryBinding.plan (1+1) from by decide)
  have draws : DefaultState.drawsBefore initial 1 ≤ DefaultState.drawsBefore initial (1+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 1 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_1 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 9#5 2#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 2), .reg (.x 3)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 9#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 9#5 2#5 3#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_1] using ob)
#print axioms site_1
#print axioms word_1
#print axioms step_1

theorem site_2 : EntryBinding.plan.code[2]? = some (7600, 2613279818) := rfl
theorem room_2 (initial : NativeState) : 2 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_2 : NativeEntryBodyDispatch.Umulh64.selected 10#5 2#5 3#5 = 2613279818#32 := by decide
theorem step_2 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 2 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (2+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[2]'(room_2 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7600, 2613279818) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 7600 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (7600, 2613279818) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (2+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 2 + 4#64 = offset EntryBinding.plan (2+1) from by decide)
  have draws : DefaultState.drawsBefore initial 2 ≤ DefaultState.drawsBefore initial (2+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 2 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_2 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 10#5 2#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 2), .reg (.x 3)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 10#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 10#5 2#5 3#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_2] using ob)
#print axioms site_2
#print axioms word_2
#print axioms step_2

theorem site_4 : EntryBinding.plan.code[4]? = some (7608, 2600827979) := rfl
theorem room_4 (initial : NativeState) : 4 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_4 : NativeEntryBodyDispatch.Madd64.selected 11#5 2#5 5#5 = 2600827979#32 := by decide
theorem step_4 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (4+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[4]'(room_4 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7608, 2600827979) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 7608 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (7608, 2600827979) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (4+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 4 + 4#64 = offset EntryBinding.plan (4+1) from by decide)
  have draws : DefaultState.drawsBefore initial 4 ≤ DefaultState.drawsBefore initial (4+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 4 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_4 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 11#5 2#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 2), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 11#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 11#5 2#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_4] using ob)
#print axioms site_4
#print axioms word_4
#print axioms step_4

theorem site_5 : EntryBinding.plan.code[5]? = some (7612, 2613410892) := rfl
theorem room_5 (initial : NativeState) : 5 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_5 : NativeEntryBodyDispatch.Umulh64.selected 12#5 2#5 5#5 = 2613410892#32 := by decide
theorem step_5 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (5+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[5]'(room_5 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7612, 2613410892) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 7612 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (7612, 2613410892) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (5+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 5 + 4#64 = offset EntryBinding.plan (5+1) from by decide)
  have draws : DefaultState.drawsBefore initial 5 ≤ DefaultState.drawsBefore initial (5+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 5 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_5 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 12#5 2#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.umulh, [.reg (.x 2), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 12#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 12#5 2#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_5] using ob)
#print axioms site_5
#print axioms word_5
#print axioms step_5

theorem site_6 : EntryBinding.plan.code[6]? = some (7616, 2600762439) := rfl
theorem room_6 (initial : NativeState) : 6 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_6 : NativeEntryBodyDispatch.Madd64.selected 7#5 2#5 4#5 = 2600762439#32 := by decide
theorem step_6 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 6 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (6+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[6]'(room_6 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7616, 2600762439) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 7616 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (7616, 2600762439) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (6+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 6 + 4#64 = offset EntryBinding.plan (6+1) from by decide)
  have draws : DefaultState.drawsBefore initial 6 ≤ DefaultState.drawsBefore initial (6+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 6 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_6 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 2#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 2), .reg (.x 4)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 2#5 4#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_6] using ob)
#print axioms site_6
#print axioms word_6
#print axioms step_6

theorem site_7 : EntryBinding.plan.code[7]? = some (7620, 2613345350) := rfl
theorem room_7 (initial : NativeState) : 7 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_7 : NativeEntryBodyDispatch.Umulh64.selected 6#5 2#5 4#5 = 2613345350#32 := by decide
theorem step_7 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 7 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (7+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[7]'(room_7 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7620, 2613345350) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 7620 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (7620, 2613345350) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (7+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 7 + 4#64 = offset EntryBinding.plan (7+1) from by decide)
  have draws : DefaultState.drawsBefore initial 7 ≤ DefaultState.drawsBefore initial (7+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 7 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_7 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 6#5 2#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 2), .reg (.x 4)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 6#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 6#5 2#5 4#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_7] using ob)
#print axioms site_7
#print axioms word_7
#print axioms step_7

theorem site_8 : EntryBinding.plan.code[8]? = some (7624, 2869363018) := rfl
theorem room_8 (initial : NativeState) : 8 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_8 : NativeEntryBodyDispatch.AddsShift64.selected 10#5 10#5 0#6 7#5 = 2869363018#32 := by decide
theorem step_8 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 8 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (8+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[8]'(room_8 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7624, 2869363018) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 7624 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (7624, 2869363018) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (8+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 8 + 4#64 = offset EntryBinding.plan (8+1) from by decide)
  have draws : DefaultState.drawsBefore initial 8 ≤ DefaultState.drawsBefore initial (8+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 8 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_8 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 10#5 10#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 10#5 10#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 10#5 10#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_8] using ob)
#print axioms site_8
#print axioms word_8
#print axioms step_8

theorem site_9 : EntryBinding.plan.code[9]? = some (7628, 3120955755) := rfl
theorem room_9 (initial : NativeState) : 9 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_9 : NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 6#5 = 3120955755#32 := by decide
theorem step_9 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 9 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (9+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[9]'(room_9 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7628, 3120955755) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 7628 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (7628, 3120955755) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (9+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 9 + 4#64 = offset EntryBinding.plan (9+1) from by decide)
  have draws : DefaultState.drawsBefore initial 9 ≤ DefaultState.drawsBefore initial (9+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 9 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_9 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 6#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 11#5 11#5 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_9] using ob)
#print axioms site_9
#print axioms word_9
#print axioms step_9

theorem site_10 : EntryBinding.plan.code[10]? = some (7632, 2600762471) := rfl
theorem room_10 (initial : NativeState) : 10 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_10 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 4#5 = 2600762471#32 := by decide
theorem step_10 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 10 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (10+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[10]'(room_10 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7632, 2600762471) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 7632 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (7632, 2600762471) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (10+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 10 + 4#64 = offset EntryBinding.plan (10+1) from by decide)
  have draws : DefaultState.drawsBefore initial 10 ≤ DefaultState.drawsBefore initial (10+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 10 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_10 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 4)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 4#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_10] using ob)
#print axioms site_10
#print axioms word_10
#print axioms step_10

theorem site_11 : EntryBinding.plan.code[11]? = some (7636, 2613345382) := rfl
theorem room_11 (initial : NativeState) : 11 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_11 : NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 4#5 = 2613345382#32 := by decide
theorem step_11 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 11 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (11+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[11]'(room_11 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7636, 2613345382) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 7636 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (7636, 2613345382) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (11+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 11 + 4#64 = offset EntryBinding.plan (11+1) from by decide)
  have draws : DefaultState.drawsBefore initial 11 ≤ DefaultState.drawsBefore initial (11+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 11 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_11 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 4)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 6#5 3#5 4#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_11] using ob)
#print axioms site_11
#print axioms word_11
#print axioms step_11

theorem site_12 : EntryBinding.plan.code[12]? = some (7640, 2585723078) := rfl
theorem room_12 (initial : NativeState) : 12 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_12 : NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5 = 2585723078#32 := by decide
theorem step_12 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 12 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (12+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[12]'(room_12 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7640, 2585723078) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 7640 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (7640, 2585723078) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (12+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 12 + 4#64 = offset EntryBinding.plan (12+1) from by decide)
  have draws : DefaultState.drawsBefore initial 12 ≤ DefaultState.drawsBefore initial (12+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 12 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_12 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 6#5 6#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_12] using ob)
#print axioms site_12
#print axioms word_12
#print axioms step_12

theorem site_13 : EntryBinding.plan.code[13]? = some (7644, 2869363051) := rfl
theorem room_13 (initial : NativeState) : 13 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_13 : NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 7#5 = 2869363051#32 := by decide
theorem step_13 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 13 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (13+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[13]'(room_13 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7644, 2869363051) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 7644 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (7644, 2869363051) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (13+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 13 + 4#64 = offset EntryBinding.plan (13+1) from by decide)
  have draws : DefaultState.drawsBefore initial 13 ≤ DefaultState.drawsBefore initial (13+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 13 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_13 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 11#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 11#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_13] using ob)
#print axioms site_13
#print axioms word_13
#print axioms step_13

theorem site_14 : EntryBinding.plan.code[14]? = some (7648, 2600828045) := rfl
theorem room_14 (initial : NativeState) : 14 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_14 : NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 5#5 = 2600828045#32 := by decide
theorem step_14 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 14 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (14+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[14]'(room_14 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7648, 2600828045) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 7648 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (7648, 2600828045) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (14+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 14 + 4#64 = offset EntryBinding.plan (14+1) from by decide)
  have draws : DefaultState.drawsBefore initial 14 ≤ DefaultState.drawsBefore initial (14+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 14 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_14 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.mul, [.reg (.x 4), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 13#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 13#5 4#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_14] using ob)
#print axioms site_14
#print axioms word_14
#print axioms step_14

theorem site_15 : EntryBinding.plan.code[15]? = some (7652, 2613410958) := rfl
theorem room_15 (initial : NativeState) : 15 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_15 : NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 5#5 = 2613410958#32 := by decide
theorem step_15 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 15 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (15+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[15]'(room_15 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7652, 2613410958) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_15
  have pc : x.regs._PC = MemReloc.imageAddress base 7652 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (7652, 2613410958) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (15+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 15 + 4#64 = offset EntryBinding.plan (15+1) from by decide)
  have draws : DefaultState.drawsBefore initial 15 ≤ DefaultState.drawsBefore initial (15+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 15 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_15 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 4), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 14#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 14#5 4#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_15] using ob)
#print axioms site_15
#print axioms word_15
#print axioms step_15

theorem site_16 : EntryBinding.plan.code[16]? = some (7656, 3120955788) := rfl
theorem room_16 (initial : NativeState) : 16 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_16 : NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 6#5 = 3120955788#32 := by decide
theorem step_16 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 16 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (16+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[16]'(room_16 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7656, 3120955788) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 7656 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (7656, 3120955788) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (16+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 16 + 4#64 = offset EntryBinding.plan (16+1) from by decide)
  have draws : DefaultState.drawsBefore initial 16 ≤ DefaultState.drawsBefore initial (16+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 16 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_16 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_16] using ob)
#print axioms site_16
#print axioms word_16
#print axioms step_16

theorem site_17 : EntryBinding.plan.code[17]? = some (7660, 2600828007) := rfl
theorem room_17 (initial : NativeState) : 17 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_17 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5 = 2600828007#32 := by decide
theorem step_17 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 17 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (17+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[17]'(room_17 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7660, 2600828007) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 7660 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (7660, 2600828007) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (17+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 17 + 4#64 = offset EntryBinding.plan (17+1) from by decide)
  have draws : DefaultState.drawsBefore initial 17 ≤ DefaultState.drawsBefore initial (17+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 17 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_17 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_17] using ob)
#print axioms site_17
#print axioms word_17
#print axioms step_17

theorem site_18 : EntryBinding.plan.code[18]? = some (7664, 2613410918) := rfl
theorem room_18 (initial : NativeState) : 18 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_18 : NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 5#5 = 2613410918#32 := by decide
theorem step_18 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 18 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (18+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[18]'(room_18 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7664, 2613410918) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 7664 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (7664, 2613410918) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (18+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 18 + 4#64 = offset EntryBinding.plan (18+1) from by decide)
  have draws : DefaultState.drawsBefore initial 18 ≤ DefaultState.drawsBefore initial (18+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 18 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_18 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 6#5 3#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_18] using ob)
#print axioms site_18
#print axioms word_18
#print axioms step_18

theorem site_19 : EntryBinding.plan.code[19]? = some (7668, 2585723078) := rfl
theorem room_19 (initial : NativeState) : 19 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_19 : NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5 = 2585723078#32 := by decide
theorem step_19 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 19 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (19+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[19]'(room_19 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7668, 2585723078) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 7668 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (7668, 2585723078) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (19+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 19 + 4#64 = offset EntryBinding.plan (19+1) from by decide)
  have draws : DefaultState.drawsBefore initial 19 ≤ DefaultState.drawsBefore initial (19+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 19 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_19 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 6#5 6#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_19] using ob)
#print axioms site_19
#print axioms word_19
#print axioms step_19

theorem site_20 : EntryBinding.plan.code[20]? = some (7672, 2869363084) := rfl
theorem room_20 (initial : NativeState) : 20 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_20 : NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 7#5 = 2869363084#32 := by decide
theorem step_20 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 20 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (20+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[20]'(room_20 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7672, 2869363084) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 7672 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (7672, 2869363084) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (20+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 20 + 4#64 = offset EntryBinding.plan (20+1) from by decide)
  have draws : DefaultState.drawsBefore initial 20 ≤ DefaultState.drawsBefore initial (20+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 20 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_20 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 12#5 12#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_20] using ob)
#print axioms site_20
#print axioms word_20
#print axioms step_20

theorem site_21 : EntryBinding.plan.code[21]? = some (7676, 3120955821) := rfl
theorem room_21 (initial : NativeState) : 21 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_21 : NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 6#5 = 3120955821#32 := by decide
theorem step_21 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 21 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (21+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[21]'(room_21 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7676, 3120955821) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 7676 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (7676, 3120955821) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (21+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 21 + 4#64 = offset EntryBinding.plan (21+1) from by decide)
  have draws : DefaultState.drawsBefore initial 21 ≤ DefaultState.drawsBefore initial (21+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 21 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_21 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 6#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 13#5 13#5 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_21] using ob)
#print axioms site_21
#print axioms word_21
#print axioms step_21

theorem site_22 : EntryBinding.plan.code[22]? = some (7680, 2585723342) := rfl
theorem room_22 (initial : NativeState) : 22 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_22 : NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5 = 2585723342#32 := by decide
theorem step_22 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 22 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (22+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[22]'(room_22 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7680, 2585723342) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 7680 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (7680, 2585723342) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (22+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 22 + 4#64 = offset EntryBinding.plan (22+1) from by decide)
  have draws : DefaultState.drawsBefore initial 22 ≤ DefaultState.drawsBefore initial (22+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 22 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_22 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_22] using ob)
#print axioms site_22
#print axioms word_22
#print axioms step_22

theorem site_23 : EntryBinding.plan.code[23]? = some (7684, 2869494057) := rfl
theorem room_23 (initial : NativeState) : 23 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_23 : NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 9#5 = 2869494057#32 := by decide
theorem step_23 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 23 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (23+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[23]'(room_23 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7684, 2869494057) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 7684 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (7684, 2869494057) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (23+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 23 + 4#64 = offset EntryBinding.plan (23+1) from by decide)
  have draws : DefaultState.drawsBefore initial 23 ≤ DefaultState.drawsBefore initial (23+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 23 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_23 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 9#5 9#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_23] using ob)
#print axioms site_23
#print axioms word_23
#print axioms step_23

theorem site_24 : EntryBinding.plan.code[24]? = some (7688, 3121217866) := rfl
theorem room_24 (initial : NativeState) : 24 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_24 : NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 10#5 = 3121217866#32 := by decide
theorem step_24 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 24 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (24+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[24]'(room_24 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7688, 3121217866) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 7688 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (7688, 3121217866) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (24+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 24 + 4#64 = offset EntryBinding.plan (24+1) from by decide)
  have draws : DefaultState.drawsBefore initial 24 ≤ DefaultState.drawsBefore initial (24+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 24 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_24 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 10#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 10#5 10#5 10#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_24] using ob)
#print axioms site_24
#print axioms word_24
#print axioms step_24

theorem site_25 : EntryBinding.plan.code[25]? = some (7692, 3121283435) := rfl
theorem room_25 (initial : NativeState) : 25 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_25 : NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 11#5 = 3121283435#32 := by decide
theorem step_25 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 25 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (25+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[25]'(room_25 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7692, 3121283435) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_25
  have pc : x.regs._PC = MemReloc.imageAddress base 7692 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    25 x inv.core (7692, 3121283435) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (25+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 25 + 4#64 = offset EntryBinding.plan (25+1) from by decide)
  have draws : DefaultState.drawsBefore initial 25 ≤ DefaultState.drawsBefore initial (25+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 25 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_25 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 11#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 11#5 11#5 11#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_25] using ob)
#print axioms site_25
#print axioms word_25
#print axioms step_25

theorem site_26 : EntryBinding.plan.code[26]? = some (7696, 3121349004) := rfl
theorem room_26 (initial : NativeState) : 26 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_26 : NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 12#5 = 3121349004#32 := by decide
theorem step_26 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 26 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (26+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[26]'(room_26 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7696, 3121349004) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_26
  have pc : x.regs._PC = MemReloc.imageAddress base 7696 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    26 x inv.core (7696, 3121349004) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (26+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 26 + 4#64 = offset EntryBinding.plan (26+1) from by decide)
  have draws : DefaultState.drawsBefore initial 26 ≤ DefaultState.drawsBefore initial (26+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 26 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_26 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 12#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 12#5 12#5 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_26] using ob)
#print axioms site_26
#print axioms word_26
#print axioms step_26

theorem site_27 : EntryBinding.plan.code[27]? = some (7700, 3121414573) := rfl
theorem room_27 (initial : NativeState) : 27 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_27 : NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 13#5 = 3121414573#32 := by decide
theorem step_27 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 27 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (27+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[27]'(room_27 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7700, 3121414573) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 7700 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (7700, 3121414573) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (27+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 27 + 4#64 = offset EntryBinding.plan (27+1) from by decide)
  have draws : DefaultState.drawsBefore initial 27 ≤ DefaultState.drawsBefore initial (27+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 27 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_27 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 13#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 13#5 13#5 13#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_27] using ob)
#print axioms site_27
#print axioms word_27
#print axioms step_27

theorem site_28 : EntryBinding.plan.code[28]? = some (7704, 3121480142) := rfl
theorem room_28 (initial : NativeState) : 28 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_28 : NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 14#5 = 3121480142#32 := by decide
theorem step_28 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 28 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (28+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[28]'(room_28 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7704, 3121480142) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_28
  have pc : x.regs._PC = MemReloc.imageAddress base 7704 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    28 x inv.core (7704, 3121480142) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (28+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 28 + 4#64 = offset EntryBinding.plan (28+1) from by decide)
  have draws : DefaultState.drawsBefore initial 28 ≤ DefaultState.drawsBefore initial (28+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 28 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_28 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 14#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 14#5 14#5 14#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_28] using ob)
#print axioms site_28
#print axioms word_28
#print axioms step_28

theorem site_29 : EntryBinding.plan.code[29]? = some (7708, 2594125798) := rfl
theorem room_29 (initial : NativeState) : 29 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_29 : NativeEntryBodyDispatch.Csinc3.selected 6#5 = 2594125798#32 := by decide
theorem step_29 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 29 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (29+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[29]'(room_29 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7708, 2594125798) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_29
  have pc : x.regs._PC = MemReloc.imageAddress base 7708 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    29 x inv.core (7708, 2594125798) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (29+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 29 + 4#64 = offset EntryBinding.plan (29+1) from by decide)
  have draws : DefaultState.drawsBefore initial 29 ≤ DefaultState.drawsBefore initial (29+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 29 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_29 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Csinc3.selected 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Csinc3.tailX real x 6#5 (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_17 real x 6#5 (by decide) (by decide)) next (by simpa only [word_29] using ob)
#print axioms site_29
#print axioms word_29
#print axioms step_29

theorem site_30 : EntryBinding.plan.code[30]? = some (7712, 2613214279) := rfl
theorem room_30 (initial : NativeState) : 30 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_30 : NativeEntryBodyDispatch.Umulh64.selected 7#5 2#5 2#5 = 2613214279#32 := by decide
theorem step_30 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 30 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (30+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[30]'(room_30 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7712, 2613214279) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_30
  have pc : x.regs._PC = MemReloc.imageAddress base 7712 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    30 x inv.core (7712, 2613214279) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (30+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 30 + 4#64 = offset EntryBinding.plan (30+1) from by decide)
  have draws : DefaultState.drawsBefore initial 30 ≤ DefaultState.drawsBefore initial (30+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 30 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_30 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 7#5 2#5 2#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 2), .reg (.x 2)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 7#5 2#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 7#5 2#5 2#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_30] using ob)
#print axioms site_30
#print axioms word_30
#print axioms step_30

theorem site_31 : EntryBinding.plan.code[31]? = some (7716, 2600631368) := rfl
theorem room_31 (initial : NativeState) : 31 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_31 : NativeEntryBodyDispatch.Madd64.selected 8#5 2#5 2#5 = 2600631368#32 := by decide
theorem step_31 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 31 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (31+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[31]'(room_31 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7716, 2600631368) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_31
  have pc : x.regs._PC = MemReloc.imageAddress base 7716 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    31 x inv.core (7716, 2600631368) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (31+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 31 + 4#64 = offset EntryBinding.plan (31+1) from by decide)
  have draws : DefaultState.drawsBefore initial 31 ≤ DefaultState.drawsBefore initial (31+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 31 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_31 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 8#5 2#5 2#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.mul, [.reg (.x 2), .reg (.x 2)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 8#5 2#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 8#5 2#5 2#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_31] using ob)
#print axioms site_31
#print axioms word_31
#print axioms step_31

theorem site_32 : EntryBinding.plan.code[32]? = some (7720, 2869362985) := rfl
theorem room_32 (initial : NativeState) : 32 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_32 : NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 7#5 = 2869362985#32 := by decide
theorem step_32 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 32 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (32+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[32]'(room_32 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7720, 2869362985) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_32
  have pc : x.regs._PC = MemReloc.imageAddress base 7720 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    32 x inv.core (7720, 2869362985) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (32+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 32 + 4#64 = offset EntryBinding.plan (32+1) from by decide)
  have draws : DefaultState.drawsBefore initial 32 ≤ DefaultState.drawsBefore initial (32+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 32 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_32 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 9#5 9#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_32] using ob)
#print axioms site_32
#print axioms word_32
#print axioms step_32

theorem site_33 : EntryBinding.plan.code[33]? = some (7724, 2600696935) := rfl
theorem room_33 (initial : NativeState) : 33 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_33 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 3#5 = 2600696935#32 := by decide
theorem step_33 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 33 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (33+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[33]'(room_33 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7724, 2600696935) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_33
  have pc : x.regs._PC = MemReloc.imageAddress base 7724 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    33 x inv.core (7724, 2600696935) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (33+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 33 + 4#64 = offset EntryBinding.plan (33+1) from by decide)
  have draws : DefaultState.drawsBefore initial 33 ≤ DefaultState.drawsBefore initial (33+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 33 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_33 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 3)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_33] using ob)
#print axioms site_33
#print axioms word_33
#print axioms step_33

theorem site_34 : EntryBinding.plan.code[34]? = some (7728, 3121021258) := rfl
theorem room_34 (initial : NativeState) : 34 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_34 : NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5 = 3121021258#32 := by decide
theorem step_34 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 34 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (34+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[34]'(room_34 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7728, 3121021258) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_34
  have pc : x.regs._PC = MemReloc.imageAddress base 7728 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    34 x inv.core (7728, 3121021258) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (34+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 34 + 4#64 = offset EntryBinding.plan (34+1) from by decide)
  have draws : DefaultState.drawsBefore initial 34 ≤ DefaultState.drawsBefore initial (34+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 34 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_34 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_34] using ob)
#print axioms site_34
#print axioms word_34
#print axioms step_34

theorem site_35 : EntryBinding.plan.code[35]? = some (7732, 2613279847) := rfl
theorem room_35 (initial : NativeState) : 35 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_35 : NativeEntryBodyDispatch.Umulh64.selected 7#5 3#5 3#5 = 2613279847#32 := by decide
theorem step_35 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 35 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (35+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[35]'(room_35 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7732, 2613279847) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_35
  have pc : x.regs._PC = MemReloc.imageAddress base 7732 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    35 x inv.core (7732, 2613279847) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (35+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 35 + 4#64 = offset EntryBinding.plan (35+1) from by decide)
  have draws : DefaultState.drawsBefore initial 35 ≤ DefaultState.drawsBefore initial (35+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 35 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_35 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 7#5 3#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 3), .reg (.x 3)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_35] using ob)
#print axioms site_35
#print axioms word_35
#print axioms step_35

theorem site_36 : EntryBinding.plan.code[36]? = some (7736, 3121021291) := rfl
theorem room_36 (initial : NativeState) : 36 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_36 : NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5 = 3121021291#32 := by decide
theorem step_36 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 36 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (36+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[36]'(room_36 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7736, 3121021291) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_36
  have pc : x.regs._PC = MemReloc.imageAddress base 7736 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    36 x inv.core (7736, 3121021291) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (36+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 36 + 4#64 = offset EntryBinding.plan (36+1) from by decide)
  have draws : DefaultState.drawsBefore initial 36 ≤ DefaultState.drawsBefore initial (36+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 36 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_36 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_36] using ob)
#print axioms site_36
#print axioms word_36
#print axioms step_36

theorem site_37 : EntryBinding.plan.code[37]? = some (7740, 2600762503) := rfl
theorem room_37 (initial : NativeState) : 37 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_37 : NativeEntryBodyDispatch.Madd64.selected 7#5 4#5 4#5 = 2600762503#32 := by decide
theorem step_37 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 37 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (37+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[37]'(room_37 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7740, 2600762503) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_37
  have pc : x.regs._PC = MemReloc.imageAddress base 7740 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    37 x inv.core (7740, 2600762503) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (37+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 37 + 4#64 = offset EntryBinding.plan (37+1) from by decide)
  have draws : DefaultState.drawsBefore initial 37 ≤ DefaultState.drawsBefore initial (37+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 37 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_37 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 4), .reg (.x 4)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_37] using ob)
#print axioms site_37
#print axioms word_37
#print axioms step_37

theorem site_38 : EntryBinding.plan.code[38]? = some (7744, 3121021324) := rfl
theorem room_38 (initial : NativeState) : 38 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_38 : NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 7#5 = 3121021324#32 := by decide
theorem step_38 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 38 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (38+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[38]'(room_38 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7744, 3121021324) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_38
  have pc : x.regs._PC = MemReloc.imageAddress base 7744 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    38 x inv.core (7744, 3121021324) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (38+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 38 + 4#64 = offset EntryBinding.plan (38+1) from by decide)
  have draws : DefaultState.drawsBefore initial 38 ≤ DefaultState.drawsBefore initial (38+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 38 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_38 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 12#5 12#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_38] using ob)
#print axioms site_38
#print axioms word_38
#print axioms step_38

theorem site_39 : EntryBinding.plan.code[39]? = some (7748, 2613345415) := rfl
theorem room_39 (initial : NativeState) : 39 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_39 : NativeEntryBodyDispatch.Umulh64.selected 7#5 4#5 4#5 = 2613345415#32 := by decide
theorem step_39 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 39 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (39+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[39]'(room_39 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7748, 2613345415) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_39
  have pc : x.regs._PC = MemReloc.imageAddress base 7748 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    39 x inv.core (7748, 2613345415) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (39+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 39 + 4#64 = offset EntryBinding.plan (39+1) from by decide)
  have draws : DefaultState.drawsBefore initial 39 ≤ DefaultState.drawsBefore initial (39+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 39 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_39 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 7#5 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 4), .reg (.x 4)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_39] using ob)
#print axioms site_39
#print axioms word_39
#print axioms step_39

theorem site_40 : EntryBinding.plan.code[40]? = some (7752, 3121021357) := rfl
theorem room_40 (initial : NativeState) : 40 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_40 : NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 7#5 = 3121021357#32 := by decide
theorem step_40 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 40 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (40+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[40]'(room_40 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7752, 3121021357) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_40
  have pc : x.regs._PC = MemReloc.imageAddress base 7752 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    40 x inv.core (7752, 3121021357) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (40+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 40 + 4#64 = offset EntryBinding.plan (40+1) from by decide)
  have draws : DefaultState.drawsBefore initial 40 ≤ DefaultState.drawsBefore initial (40+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 40 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_40 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 13#5 13#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_40] using ob)
#print axioms site_40
#print axioms word_40
#print axioms step_40

theorem site_41 : EntryBinding.plan.code[41]? = some (7756, 2600828071) := rfl
theorem room_41 (initial : NativeState) : 41 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_41 : NativeEntryBodyDispatch.Madd64.selected 7#5 5#5 5#5 = 2600828071#32 := by decide
theorem step_41 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 41 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (41+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[41]'(room_41 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7756, 2600828071) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_41
  have pc : x.regs._PC = MemReloc.imageAddress base 7756 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    41 x inv.core (7756, 2600828071) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (41+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 41 + 4#64 = offset EntryBinding.plan (41+1) from by decide)
  have draws : DefaultState.drawsBefore initial 41 ≤ DefaultState.drawsBefore initial (41+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 41 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_41 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 5), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_41] using ob)
#print axioms site_41
#print axioms word_41
#print axioms step_41

theorem site_42 : EntryBinding.plan.code[42]? = some (7760, 3121021390) := rfl
theorem room_42 (initial : NativeState) : 42 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_42 : NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 7#5 = 3121021390#32 := by decide
theorem step_42 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 42 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (42+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[42]'(room_42 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7760, 3121021390) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_42
  have pc : x.regs._PC = MemReloc.imageAddress base 7760 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    42 x inv.core (7760, 3121021390) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (42+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 42 + 4#64 = offset EntryBinding.plan (42+1) from by decide)
  have draws : DefaultState.drawsBefore initial 42 ≤ DefaultState.drawsBefore initial (42+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 42 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_42 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 14#5 14#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_42] using ob)
#print axioms site_42
#print axioms word_42
#print axioms step_42

theorem site_43 : EntryBinding.plan.code[43]? = some (7764, 2613410983) := rfl
theorem room_43 (initial : NativeState) : 43 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_43 : NativeEntryBodyDispatch.Umulh64.selected 7#5 5#5 5#5 = 2613410983#32 := by decide
theorem step_43 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 43 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (43+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[43]'(room_43 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7764, 2613410983) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_43
  have pc : x.regs._PC = MemReloc.imageAddress base 7764 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    43 x inv.core (7764, 2613410983) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (43+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 43 + 4#64 = offset EntryBinding.plan (43+1) from by decide)
  have draws : DefaultState.drawsBefore initial 43 ≤ DefaultState.drawsBefore initial (43+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 43 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_43 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 7#5 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 5), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_43] using ob)
#print axioms site_43
#print axioms word_43
#print axioms step_43

theorem site_44 : EntryBinding.plan.code[44]? = some (7768, 2584150214) := rfl
theorem room_44 (initial : NativeState) : 44 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_44 : NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 7#5 = 2584150214#32 := by decide
theorem step_44 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 44 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (44+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[44]'(room_44 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7768, 2584150214) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_44
  have pc : x.regs._PC = MemReloc.imageAddress base 7768 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    44 x inv.core (7768, 2584150214) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (44+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 44 + 4#64 = offset EntryBinding.plan (44+1) from by decide)
  have draws : DefaultState.drawsBefore initial 44 ≤ DefaultState.drawsBefore initial (44+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 44 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_44 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 7), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 6#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 6#5 6#5 7#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_44] using ob)
#print axioms site_44
#print axioms word_44
#print axioms step_44

theorem site_45 : EntryBinding.plan.code[45]? = some (7772, 3531635235) := rfl
theorem room_45 (initial : NativeState) : 45 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_45 : NativeEntryBodyDispatch.Movz64z.selected 3#5 977#16 = 3531635235#32 := by decide
theorem step_45 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 45 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (45+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[45]'(room_45 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7772, 3531635235) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_45
  have pc : x.regs._PC = MemReloc.imageAddress base 7772 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    45 x inv.core (7772, 3531635235) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (45+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 45 + 4#64 = offset EntryBinding.plan (45+1) from by decide)
  have draws : DefaultState.drawsBefore initial 45 ≤ DefaultState.drawsBefore initial (45+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 45 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_45 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Movz64z.selected 3#5 977#16) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨(.const 977#64), []⟩)] (none) (by rfl) x inv
    (ArmCertValue.Movz64z.tailX real x 3#5 977#16 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_2 real x 3#5 977#16 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_45] using ob)
#print axioms site_45
#print axioms word_45
#print axioms step_45

theorem site_46 : EntryBinding.plan.code[46]? = some (7776, 2992636003) := rfl
theorem room_46 (initial : NativeState) : 46 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_46 : NativeEntryBodyDispatch.OrrImm32_0.selected 3#5 3#5 = 2992636003#32 := by decide
theorem step_46 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 46 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (46+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[46]'(room_46 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7776, 2992636003) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_46
  have pc : x.regs._PC = MemReloc.imageAddress base 7776 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    46 x inv.core (7776, 2992636003) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (46+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 46 + 4#64 = offset EntryBinding.plan (46+1) from by decide)
  have draws : DefaultState.drawsBefore initial 46 ≤ DefaultState.drawsBefore initial (46+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 46 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_46 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.OrrImm32_0.selected 3#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.orr, [.reg (.x 3), .lit 4294967296#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.OrrImm32_0.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_8 real x 3#5 3#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_46] using ob)
#print axioms site_46
#print axioms word_46
#print axioms step_46

theorem site_47 : EntryBinding.plan.code[47]? = some (7780, 2601286759) := rfl
theorem room_47 (initial : NativeState) : 47 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_47 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 12#5 = 2601286759#32 := by decide
theorem step_47 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 47 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (47+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[47]'(room_47 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7780, 2601286759) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_47
  have pc : x.regs._PC = MemReloc.imageAddress base 7780 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    47 x inv.core (7780, 2601286759) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (47+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 47 + 4#64 = offset EntryBinding.plan (47+1) from by decide)
  have draws : DefaultState.drawsBefore initial 47 ≤ DefaultState.drawsBefore initial (47+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 47 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_47 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 12)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 12#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 12#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_47] using ob)
#print axioms site_47
#print axioms word_47
#print axioms step_47

theorem site_48 : EntryBinding.plan.code[48]? = some (7784, 2613869668) := rfl
theorem room_48 (initial : NativeState) : 48 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_48 : NativeEntryBodyDispatch.Umulh64.selected 4#5 3#5 12#5 = 2613869668#32 := by decide
theorem step_48 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 48 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (48+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[48]'(room_48 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7784, 2613869668) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_48
  have pc : x.regs._PC = MemReloc.imageAddress base 7784 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    48 x inv.core (7784, 2613869668) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (48+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 48 + 4#64 = offset EntryBinding.plan (48+1) from by decide)
  have draws : DefaultState.drawsBefore initial 48 ≤ DefaultState.drawsBefore initial (48+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 48 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_48 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 4#5 3#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 3), .reg (.x 12)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 4#5 3#5 12#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 4#5 3#5 12#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_48] using ob)
#print axioms site_48
#print axioms word_48
#print axioms step_48

theorem site_49 : EntryBinding.plan.code[49]? = some (7788, 2869362952) := rfl
theorem room_49 (initial : NativeState) : 49 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_49 : NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5 = 2869362952#32 := by decide
theorem step_49 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 49 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (49+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[49]'(room_49 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7788, 2869362952) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_49
  have pc : x.regs._PC = MemReloc.imageAddress base 7788 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    49 x inv.core (7788, 2869362952) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (49+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 49 + 4#64 = offset EntryBinding.plan (49+1) from by decide)
  have draws : DefaultState.drawsBefore initial 49 ≤ DefaultState.drawsBefore initial (49+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 49 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_49 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_49] using ob)
#print axioms site_49
#print axioms word_49
#print axioms step_49

theorem site_50 : EntryBinding.plan.code[50]? = some (7792, 2601352295) := rfl
theorem room_50 (initial : NativeState) : 50 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_50 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 13#5 = 2601352295#32 := by decide
theorem step_50 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 50 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (50+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[50]'(room_50 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7792, 2601352295) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_50
  have pc : x.regs._PC = MemReloc.imageAddress base 7792 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    50 x inv.core (7792, 2601352295) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (50+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 50 + 4#64 = offset EntryBinding.plan (50+1) from by decide)
  have draws : DefaultState.drawsBefore initial 50 ≤ DefaultState.drawsBefore initial (50+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 50 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_50 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 13)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 13#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_50] using ob)
#print axioms site_50
#print axioms word_50
#print axioms step_50

theorem site_51 : EntryBinding.plan.code[51]? = some (7796, 2613935213) := rfl
theorem room_51 (initial : NativeState) : 51 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_51 : NativeEntryBodyDispatch.Umulh64.selected 13#5 3#5 13#5 = 2613935213#32 := by decide
theorem step_51 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 51 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (51+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[51]'(room_51 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7796, 2613935213) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_51
  have pc : x.regs._PC = MemReloc.imageAddress base 7796 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    51 x inv.core (7796, 2613935213) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (51+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 51 + 4#64 = offset EntryBinding.plan (51+1) from by decide)
  have draws : DefaultState.drawsBefore initial 51 ≤ DefaultState.drawsBefore initial (51+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 51 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_51 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 13#5 3#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 3), .reg (.x 13)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_51] using ob)
#print axioms site_51
#print axioms word_51
#print axioms step_51

theorem site_52 : EntryBinding.plan.code[52]? = some (7800, 3121021225) := rfl
theorem room_52 (initial : NativeState) : 52 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_52 : NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 7#5 = 3121021225#32 := by decide
theorem step_52 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 52 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (52+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[52]'(room_52 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7800, 3121021225) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_52
  have pc : x.regs._PC = MemReloc.imageAddress base 7800 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    52 x inv.core (7800, 3121021225) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (52+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 52 + 4#64 = offset EntryBinding.plan (52+1) from by decide)
  have draws : DefaultState.drawsBefore initial 52 ≤ DefaultState.drawsBefore initial (52+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 52 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_52 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 9#5 9#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_52] using ob)
#print axioms site_52
#print axioms word_52
#print axioms step_52

theorem site_53 : EntryBinding.plan.code[53]? = some (7804, 2601417831) := rfl
theorem room_53 (initial : NativeState) : 53 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_53 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 14#5 = 2601417831#32 := by decide
theorem step_53 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 53 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (53+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[53]'(room_53 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7804, 2601417831) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_53
  have pc : x.regs._PC = MemReloc.imageAddress base 7804 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    53 x inv.core (7804, 2601417831) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (53+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 53 + 4#64 = offset EntryBinding.plan (53+1) from by decide)
  have draws : DefaultState.drawsBefore initial 53 ≤ DefaultState.drawsBefore initial (53+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 53 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_53 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 14)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 14#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_53] using ob)
#print axioms site_53
#print axioms word_53
#print axioms step_53

theorem site_54 : EntryBinding.plan.code[54]? = some (7808, 2614000750) := rfl
theorem room_54 (initial : NativeState) : 54 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_54 : NativeEntryBodyDispatch.Umulh64.selected 14#5 3#5 14#5 = 2614000750#32 := by decide
theorem step_54 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 54 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (54+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[54]'(room_54 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7808, 2614000750) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_54
  have pc : x.regs._PC = MemReloc.imageAddress base 7808 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    54 x inv.core (7808, 2614000750) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (54+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 54 + 4#64 = offset EntryBinding.plan (54+1) from by decide)
  have draws : DefaultState.drawsBefore initial 54 ≤ DefaultState.drawsBefore initial (54+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 54 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_54 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 14#5 3#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 3), .reg (.x 14)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 14#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 14#5 3#5 14#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_54] using ob)
#print axioms site_54
#print axioms word_54
#print axioms step_54

theorem site_55 : EntryBinding.plan.code[55]? = some (7812, 3121021258) := rfl
theorem room_55 (initial : NativeState) : 55 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_55 : NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5 = 3121021258#32 := by decide
theorem step_55 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 55 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (55+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[55]'(room_55 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7812, 3121021258) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_55
  have pc : x.regs._PC = MemReloc.imageAddress base 7812 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    55 x inv.core (7812, 3121021258) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (55+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 55 + 4#64 = offset EntryBinding.plan (55+1) from by decide)
  have draws : DefaultState.drawsBefore initial 55 ≤ DefaultState.drawsBefore initial (55+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 55 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_55 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_55] using ob)
#print axioms site_55
#print axioms word_55
#print axioms step_55

theorem site_56 : EntryBinding.plan.code[56]? = some (7816, 2600893543) := rfl
theorem room_56 (initial : NativeState) : 56 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_56 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 6#5 = 2600893543#32 := by decide
theorem step_56 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 56 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (56+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[56]'(room_56 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7816, 2600893543) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_56
  have pc : x.regs._PC = MemReloc.imageAddress base 7816 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    56 x inv.core (7816, 2600893543) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (56+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 56 + 4#64 = offset EntryBinding.plan (56+1) from by decide)
  have draws : DefaultState.drawsBefore initial 56 ≤ DefaultState.drawsBefore initial (56+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 56 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_56 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_56] using ob)
#print axioms site_56
#print axioms word_56
#print axioms step_56

theorem site_57 : EntryBinding.plan.code[57]? = some (7820, 2613476454) := rfl
theorem room_57 (initial : NativeState) : 57 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_57 : NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 6#5 = 2613476454#32 := by decide
theorem step_57 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 57 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (57+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[57]'(room_57 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7820, 2613476454) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_57
  have pc : x.regs._PC = MemReloc.imageAddress base 7820 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    57 x inv.core (7820, 2613476454) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (57+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 57 + 4#64 = offset EntryBinding.plan (57+1) from by decide)
  have draws : DefaultState.drawsBefore initial 57 ≤ DefaultState.drawsBefore initial (57+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 57 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_57 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 6#5 3#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_57] using ob)
#print axioms site_57
#print axioms word_57
#print axioms step_57

theorem site_58 : EntryBinding.plan.code[58]? = some (7824, 3121021291) := rfl
theorem room_58 (initial : NativeState) : 58 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_58 : NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5 = 3121021291#32 := by decide
theorem step_58 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 58 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (58+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[58]'(room_58 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7824, 3121021291) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_58
  have pc : x.regs._PC = MemReloc.imageAddress base 7824 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    58 x inv.core (7824, 3121021291) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (58+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 58 + 4#64 = offset EntryBinding.plan (58+1) from by decide)
  have draws : DefaultState.drawsBefore initial 58 ≤ DefaultState.drawsBefore initial (58+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 58 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_58 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_58] using ob)
#print axioms site_58
#print axioms word_58
#print axioms step_58

theorem site_59 : EntryBinding.plan.code[59]? = some (7828, 2594125804) := rfl
theorem room_59 (initial : NativeState) : 59 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_59 : NativeEntryBodyDispatch.Csinc3.selected 12#5 = 2594125804#32 := by decide
theorem step_59 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 59 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (59+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[59]'(room_59 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7828, 2594125804) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_59
  have pc : x.regs._PC = MemReloc.imageAddress base 7828 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    59 x inv.core (7828, 2594125804) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (59+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 59 + 4#64 = offset EntryBinding.plan (59+1) from by decide)
  have draws : DefaultState.drawsBefore initial 59 ≤ DefaultState.drawsBefore initial (59+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 59 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_59 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Csinc3.selected 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Csinc3.tailX real x 12#5 (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_17 real x 12#5 (by decide) (by decide)) next (by simpa only [word_59] using ob)
#print axioms site_59
#print axioms word_59
#print axioms step_59

theorem site_60 : EntryBinding.plan.code[60]? = some (7832, 2869166377) := rfl
theorem room_60 (initial : NativeState) : 60 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_60 : NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 4#5 = 2869166377#32 := by decide
theorem step_60 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 60 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (60+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[60]'(room_60 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7832, 2869166377) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_60
  have pc : x.regs._PC = MemReloc.imageAddress base 7832 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    60 x inv.core (7832, 2869166377) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (60+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 60 + 4#64 = offset EntryBinding.plan (60+1) from by decide)
  have draws : DefaultState.drawsBefore initial 60 ≤ DefaultState.drawsBefore initial (60+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 60 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_60 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 9#5 9#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_60] using ob)
#print axioms site_60
#print axioms word_60
#print axioms step_60

theorem site_61 : EntryBinding.plan.code[61]? = some (7836, 3121414474) := rfl
theorem room_61 (initial : NativeState) : 61 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_61 : NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5 = 3121414474#32 := by decide
theorem step_61 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 61 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (61+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[61]'(room_61 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7836, 3121414474) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_61
  have pc : x.regs._PC = MemReloc.imageAddress base 7836 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    61 x inv.core (7836, 3121414474) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (61+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 61 + 4#64 = offset EntryBinding.plan (61+1) from by decide)
  have draws : DefaultState.drawsBefore initial 61 ≤ DefaultState.drawsBefore initial (61+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 61 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_61 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_61] using ob)
#print axioms site_61
#print axioms word_61
#print axioms step_61

theorem site_62 : EntryBinding.plan.code[62]? = some (7840, 3121480043) := rfl
theorem room_62 (initial : NativeState) : 62 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_62 : NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 14#5 = 3121480043#32 := by decide
theorem step_62 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 62 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (62+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[62]'(room_62 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7840, 3121480043) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_62
  have pc : x.regs._PC = MemReloc.imageAddress base 7840 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    62 x inv.core (7840, 3121480043) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (62+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 62 + 4#64 = offset EntryBinding.plan (62+1) from by decide)
  have draws : DefaultState.drawsBefore initial 62 ≤ DefaultState.drawsBefore initial (62+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 62 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_62 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_62] using ob)
#print axioms site_62
#print axioms word_62
#print axioms step_62

theorem site_63 : EntryBinding.plan.code[63]? = some (7844, 2584084876) := rfl
theorem room_63 (initial : NativeState) : 63 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_63 : NativeEntryBodyDispatch.Adc64.selected 12#5 12#5 6#5 = 2584084876#32 := by decide
theorem step_63 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 63 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (63+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[63]'(room_63 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7844, 2584084876) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_63
  have pc : x.regs._PC = MemReloc.imageAddress base 7844 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    63 x inv.core (7844, 2584084876) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (63+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 63 + 4#64 = offset EntryBinding.plan (63+1) from by decide)
  have draws : DefaultState.drawsBefore initial 63 ≤ DefaultState.drawsBefore initial (63+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 63 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_63 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 12#5 12#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_63] using ob)
#print axioms site_63
#print axioms word_63
#print axioms step_63

theorem site_64 : EntryBinding.plan.code[64]? = some (7848, 2432697730) := rfl
theorem room_64 (initial : NativeState) : 64 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_64 : NativeEntryBodyDispatch.AddImm64.selected 2#5 12#5 1#12 = 2432697730#32 := by decide
theorem step_64 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 64 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (64+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[64]'(room_64 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7848, 2432697730) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_64
  have pc : x.regs._PC = MemReloc.imageAddress base 7848 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    64 x inv.core (7848, 2432697730) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (64+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 64 + 4#64 = offset EntryBinding.plan (64+1) from by decide)
  have draws : DefaultState.drawsBefore initial 64 ≤ DefaultState.drawsBefore initial (64+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 64 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_64 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddImm64.selected 2#5 12#5 1#12) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨.add, [.reg (.x 12), .lit 1#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.AddImm64.tailX real x 2#5 12#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) (TranslateScalarTagCheck.Tails.tail_1 real x 2#5 12#5 1#12 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_64] using ob)
#print axioms site_64
#print axioms word_64
#print axioms step_64

theorem site_65 : EntryBinding.plan.code[65]? = some (7852, 2600631399) := rfl
theorem room_65 (initial : NativeState) : 65 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_65 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 2#5 = 2600631399#32 := by decide
theorem step_65 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 65 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (65+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[65]'(room_65 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7852, 2600631399) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_65
  have pc : x.regs._PC = MemReloc.imageAddress base 7852 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    65 x inv.core (7852, 2600631399) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (65+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 65 + 4#64 = offset EntryBinding.plan (65+1) from by decide)
  have draws : DefaultState.drawsBefore initial 65 ≤ DefaultState.drawsBefore initial (65+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 65 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_65 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 2#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 2)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 2#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_65] using ob)
#print axioms site_65
#print axioms word_65
#print axioms step_65

theorem site_66 : EntryBinding.plan.code[66]? = some (7856, 2613214310) := rfl
theorem room_66 (initial : NativeState) : 66 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_66 : NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 2#5 = 2613214310#32 := by decide
theorem step_66 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 66 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (66+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[66]'(room_66 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7856, 2613214310) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_66
  have pc : x.regs._PC = MemReloc.imageAddress base 7856 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    66 x inv.core (7856, 2613214310) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (66+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 66 + 4#64 = offset EntryBinding.plan (66+1) from by decide)
  have draws : DefaultState.drawsBefore initial 66 ≤ DefaultState.drawsBefore initial (66+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 66 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_66 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 2#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 2)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 6#5 3#5 2#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_66] using ob)
#print axioms site_66
#print axioms word_66
#print axioms step_66

theorem site_67 : EntryBinding.plan.code[67]? = some (7860, 2869362952) := rfl
theorem room_67 (initial : NativeState) : 67 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_67 : NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5 = 2869362952#32 := by decide
theorem step_67 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 67 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (67+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[67]'(room_67 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7860, 2869362952) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_67
  have pc : x.regs._PC = MemReloc.imageAddress base 7860 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    67 x inv.core (7860, 2869362952) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (67+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 67 + 4#64 = offset EntryBinding.plan (67+1) from by decide)
  have draws : DefaultState.drawsBefore initial 67 ≤ DefaultState.drawsBefore initial (67+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 67 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_67 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_67] using ob)
#print axioms site_67
#print axioms word_67
#print axioms step_67

theorem site_68 : EntryBinding.plan.code[68]? = some (7864, 3120955689) := rfl
theorem room_68 (initial : NativeState) : 68 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_68 : NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5 = 3120955689#32 := by decide
theorem step_68 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 68 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (68+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[68]'(room_68 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7864, 3120955689) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_68
  have pc : x.regs._PC = MemReloc.imageAddress base 7864 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    68 x inv.core (7864, 3120955689) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (68+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 68 + 4#64 = offset EntryBinding.plan (68+1) from by decide)
  have draws : DefaultState.drawsBefore initial 68 ≤ DefaultState.drawsBefore initial (68+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 68 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_68 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_68] using ob)
#print axioms site_68
#print axioms word_68
#print axioms step_68

theorem site_69 : EntryBinding.plan.code[69]? = some (7868, 3122594122) := rfl
theorem room_69 (initial : NativeState) : 69 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_69 : NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5 = 3122594122#32 := by decide
theorem step_69 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 69 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (69+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[69]'(room_69 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7868, 3122594122) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_69
  have pc : x.regs._PC = MemReloc.imageAddress base 7868 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    69 x inv.core (7868, 3122594122) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (69+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 69 + 4#64 = offset EntryBinding.plan (69+1) from by decide)
  have draws : DefaultState.drawsBefore initial 69 ≤ DefaultState.drawsBefore initial (69+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 69 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_69 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 10#5 10#5 (by decide) (by decide) (by decide)) next (by simpa only [word_69] using ob)
#print axioms site_69
#print axioms word_69
#print axioms step_69

theorem site_70 : EntryBinding.plan.code[70]? = some (7872, 3122594155) := rfl
theorem room_70 (initial : NativeState) : 70 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_70 : NativeEntryBodyDispatch.Adcs64ZRm.selected 11#5 11#5 = 3122594155#32 := by decide
theorem step_70 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 70 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (70+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[70]'(room_70 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7872, 3122594155) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_70
  have pc : x.regs._PC = MemReloc.imageAddress base 7872 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    70 x inv.core (7872, 3122594155) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (70+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 70 + 4#64 = offset EntryBinding.plan (70+1) from by decide)
  have draws : DefaultState.drawsBefore initial 70 ≤ DefaultState.drawsBefore initial (70+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 70 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_70 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 11#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 11#5 11#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 11#5 11#5 (by decide) (by decide) (by decide)) next (by simpa only [word_70] using ob)
#print axioms site_70
#print axioms word_70
#print axioms step_70

theorem site_71 : EntryBinding.plan.code[71]? = some (7876, 2594123875) := rfl
theorem room_71 (initial : NativeState) : 71 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_71 : NativeEntryBodyDispatch.Csel3.selected 3#5 3#5 = 2594123875#32 := by decide
theorem step_71 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 71 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (71+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[71]'(room_71 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7876, 2594123875) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_71
  have pc : x.regs._PC = MemReloc.imageAddress base 7876 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    71 x inv.core (7876, 2594123875) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (71+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 71 + 4#64 = offset EntryBinding.plan (71+1) from by decide)
  have draws : DefaultState.drawsBefore initial 71 ≤ DefaultState.drawsBefore initial (71+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 71 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_71 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Csel3.selected 3#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 3), .lit 0#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Csel3.tailX real x 3#5 3#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_16 real x 3#5 3#5 (by decide) (by decide) (by decide)) next (by simpa only [word_71] using ob)
#print axioms site_71
#print axioms word_71
#print axioms step_71

theorem site_72 : EntryBinding.plan.code[72]? = some (7880, 3942842632) := rfl
theorem room_72 (initial : NativeState) : 72 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_72 : NativeEntryBodyDispatch.SubsShift64.selected 8#5 8#5 0#6 3#5 = 3942842632#32 := by decide
theorem step_72 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 72 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (72+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[72]'(room_72 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7880, 3942842632) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_72
  have pc : x.regs._PC = MemReloc.imageAddress base 7880 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    72 x inv.core (7880, 3942842632) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (72+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 72 + 4#64 = offset EntryBinding.plan (72+1) from by decide)
  have draws : DefaultState.drawsBefore initial 72 ≤ DefaultState.drawsBefore initial (72+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 72 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_72 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 8#5 8#5 0#6 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.sbc3, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 8#5 8#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 8#5 8#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_72] using ob)
#print axioms site_72
#print axioms word_72
#print axioms step_72

theorem site_73 : EntryBinding.plan.code[73]? = some (7884, 4196335913) := rfl
theorem room_73 (initial : NativeState) : 73 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_73 : NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5 = 4196335913#32 := by decide
theorem step_73 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 73 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (73+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[73]'(room_73 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7884, 4196335913) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_73
  have pc : x.regs._PC = MemReloc.imageAddress base 7884 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    73 x inv.core (7884, 4196335913) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (73+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 73 + 4#64 = offset EntryBinding.plan (73+1) from by decide)
  have draws : DefaultState.drawsBefore initial 73 ≤ DefaultState.drawsBefore initial (73+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 73 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_73 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.sbc3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_18 real x 9#5 9#5 (by decide) (by decide) (by decide)) next (by simpa only [word_73] using ob)
#print axioms site_73
#print axioms word_73
#print axioms step_73

theorem site_74 : EntryBinding.plan.code[74]? = some (7888, 4196335946) := rfl
theorem room_74 (initial : NativeState) : 74 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_74 : NativeEntryBodyDispatch.Sbcs64.selected 10#5 10#5 = 4196335946#32 := by decide
theorem step_74 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 74 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (74+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[74]'(room_74 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7888, 4196335946) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_74
  have pc : x.regs._PC = MemReloc.imageAddress base 7888 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    74 x inv.core (7888, 4196335946) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (74+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 74 + 4#64 = offset EntryBinding.plan (74+1) from by decide)
  have draws : DefaultState.drawsBefore initial 74 ≤ DefaultState.drawsBefore initial (74+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 74 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_74 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64.selected 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_18 real x 10#5 10#5 (by decide) (by decide) (by decide)) next (by simpa only [word_74] using ob)
#print axioms site_74
#print axioms word_74
#print axioms step_74

theorem site_75 : EntryBinding.plan.code[75]? = some (7892, 3659465067) := rfl
theorem room_75 (initial : NativeState) : 75 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_75 : NativeEntryBodyDispatch.Sbc64.selected 11#5 11#5 = 3659465067#32 := by decide
theorem step_75 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 75 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (75+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[75]'(room_75 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7892, 3659465067) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_75
  have pc : x.regs._PC = MemReloc.imageAddress base 7892 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    75 x inv.core (7892, 3659465067) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (75+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 75 + 4#64 = offset EntryBinding.plan (75+1) from by decide)
  have draws : DefaultState.drawsBefore initial 75 ≤ DefaultState.drawsBefore initial (75+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 75 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_75 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbc64.selected 11#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Sbc64.tailX real x 11#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_7 real x 11#5 11#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_75] using ob)
#print axioms site_75
#print axioms word_75
#print axioms step_75

theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (k : Nat) (room : k < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length)
    (selected : k ∈ ([1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75] : List Nat))
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'room) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_1 real raw config rows mapping base initial topology layout page x inv
  · exact step_2 real raw config rows mapping base initial topology layout page x inv
  · exact step_4 real raw config rows mapping base initial topology layout page x inv
  · exact step_5 real raw config rows mapping base initial topology layout page x inv
  · exact step_6 real raw config rows mapping base initial topology layout page x inv
  · exact step_7 real raw config rows mapping base initial topology layout page x inv
  · exact step_8 real raw config rows mapping base initial topology layout page x inv
  · exact step_9 real raw config rows mapping base initial topology layout page x inv
  · exact step_10 real raw config rows mapping base initial topology layout page x inv
  · exact step_11 real raw config rows mapping base initial topology layout page x inv
  · exact step_12 real raw config rows mapping base initial topology layout page x inv
  · exact step_13 real raw config rows mapping base initial topology layout page x inv
  · exact step_14 real raw config rows mapping base initial topology layout page x inv
  · exact step_15 real raw config rows mapping base initial topology layout page x inv
  · exact step_16 real raw config rows mapping base initial topology layout page x inv
  · exact step_17 real raw config rows mapping base initial topology layout page x inv
  · exact step_18 real raw config rows mapping base initial topology layout page x inv
  · exact step_19 real raw config rows mapping base initial topology layout page x inv
  · exact step_20 real raw config rows mapping base initial topology layout page x inv
  · exact step_21 real raw config rows mapping base initial topology layout page x inv
  · exact step_22 real raw config rows mapping base initial topology layout page x inv
  · exact step_23 real raw config rows mapping base initial topology layout page x inv
  · exact step_24 real raw config rows mapping base initial topology layout page x inv
  · exact step_25 real raw config rows mapping base initial topology layout page x inv
  · exact step_26 real raw config rows mapping base initial topology layout page x inv
  · exact step_27 real raw config rows mapping base initial topology layout page x inv
  · exact step_28 real raw config rows mapping base initial topology layout page x inv
  · exact step_29 real raw config rows mapping base initial topology layout page x inv
  · exact step_30 real raw config rows mapping base initial topology layout page x inv
  · exact step_31 real raw config rows mapping base initial topology layout page x inv
  · exact step_32 real raw config rows mapping base initial topology layout page x inv
  · exact step_33 real raw config rows mapping base initial topology layout page x inv
  · exact step_34 real raw config rows mapping base initial topology layout page x inv
  · exact step_35 real raw config rows mapping base initial topology layout page x inv
  · exact step_36 real raw config rows mapping base initial topology layout page x inv
  · exact step_37 real raw config rows mapping base initial topology layout page x inv
  · exact step_38 real raw config rows mapping base initial topology layout page x inv
  · exact step_39 real raw config rows mapping base initial topology layout page x inv
  · exact step_40 real raw config rows mapping base initial topology layout page x inv
  · exact step_41 real raw config rows mapping base initial topology layout page x inv
  · exact step_42 real raw config rows mapping base initial topology layout page x inv
  · exact step_43 real raw config rows mapping base initial topology layout page x inv
  · exact step_44 real raw config rows mapping base initial topology layout page x inv
  · exact step_45 real raw config rows mapping base initial topology layout page x inv
  · exact step_46 real raw config rows mapping base initial topology layout page x inv
  · exact step_47 real raw config rows mapping base initial topology layout page x inv
  · exact step_48 real raw config rows mapping base initial topology layout page x inv
  · exact step_49 real raw config rows mapping base initial topology layout page x inv
  · exact step_50 real raw config rows mapping base initial topology layout page x inv
  · exact step_51 real raw config rows mapping base initial topology layout page x inv
  · exact step_52 real raw config rows mapping base initial topology layout page x inv
  · exact step_53 real raw config rows mapping base initial topology layout page x inv
  · exact step_54 real raw config rows mapping base initial topology layout page x inv
  · exact step_55 real raw config rows mapping base initial topology layout page x inv
  · exact step_56 real raw config rows mapping base initial topology layout page x inv
  · exact step_57 real raw config rows mapping base initial topology layout page x inv
  · exact step_58 real raw config rows mapping base initial topology layout page x inv
  · exact step_59 real raw config rows mapping base initial topology layout page x inv
  · exact step_60 real raw config rows mapping base initial topology layout page x inv
  · exact step_61 real raw config rows mapping base initial topology layout page x inv
  · exact step_62 real raw config rows mapping base initial topology layout page x inv
  · exact step_63 real raw config rows mapping base initial topology layout page x inv
  · exact step_64 real raw config rows mapping base initial topology layout page x inv
  · exact step_65 real raw config rows mapping base initial topology layout page x inv
  · exact step_66 real raw config rows mapping base initial topology layout page x inv
  · exact step_67 real raw config rows mapping base initial topology layout page x inv
  · exact step_68 real raw config rows mapping base initial topology layout page x inv
  · exact step_69 real raw config rows mapping base initial topology layout page x inv
  · exact step_70 real raw config rows mapping base initial topology layout page x inv
  · exact step_71 real raw config rows mapping base initial topology layout page x inv
  · exact step_72 real raw config rows mapping base initial topology layout page x inv
  · exact step_73 real raw config rows mapping base initial topology layout page x inv
  · exact step_74 real raw config rows mapping base initial topology layout page x inv
  · exact step_75 real raw config rows mapping base initial topology layout page x inv
#print axioms all_steps

end PipeLean_D234_SecpSqrAlt_c27.DitBodyScalar
