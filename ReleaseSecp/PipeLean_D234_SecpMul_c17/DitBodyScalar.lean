import PipeLean_D234_SecpMul_c17.DitBodyState
import DitShim243.RawFetch
import PipeLean_D234_SecpMul_c17.DefaultState
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
import ArmCertValueTail.Sbcs64Reg
import ArmCertValueTail.SecpAndMask32
import ArmCertValueTail.SecpCsinv2ZZ
import ArmCertValueTail.SecpEor64
import ArmCertValueTail.SecpLsr32
import ArmCertValueTail.SecpSbc64
import ArmCertValueTail.SubsShift64
import ArmCertValueTail.Umulh64
import N1D226.AdcZeroRn64Generic.Value
import N1D226.AddsShift64Generic.Value
import N1D226.CmnImm64Generic.Value
import N1D226.CsinvCs64Generic.Value
import N1D226.CsnegCs64Generic.Value
import N1D226.Madd64Generic.DriverValue
import TranslateScalarTagCheck.Runtime
import TranslateScalarTagCheck.Secp
import TranslateScalarTagCheck.Tails
import TranslateSpan.ConditionalExprCuts
import TranslateSpan.DefaultScalar
import TranslateSpan.NativeExprCuts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMul_c17.DitBodyScalar

theorem site_2 : EntryBinding.plan.code[2]? = some (6020, 2600828007) := rfl
theorem room_2 (initial : NativeState) : 2 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_2 : NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5 = 2600828007#32 := by decide
theorem step_2 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 2 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (2+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[2]'(room_2 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6020, 2600828007) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 6020 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (6020, 2600828007) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (2+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 2 + 4#64 = offset EntryBinding.plan (2+1) from by decide)
  have draws : DefaultState.drawsBefore initial 2 ≤ DefaultState.drawsBefore initial (2+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 2 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_2 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_2] using ob)
#print axioms site_2
#print axioms word_2
#print axioms step_2

theorem site_3 : EntryBinding.plan.code[3]? = some (6024, 2613410920) := rfl
theorem room_3 (initial : NativeState) : 3 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_3 : NativeEntryBodyDispatch.Umulh64.selected 8#5 3#5 5#5 = 2613410920#32 := by decide
theorem step_3 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 3 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (3+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[3]'(room_3 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6024, 2613410920) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 6024 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (6024, 2613410920) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (3+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 3 + 4#64 = offset EntryBinding.plan (3+1) from by decide)
  have draws : DefaultState.drawsBefore initial 3 ≤ DefaultState.drawsBefore initial (3+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 3 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_3 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 8#5 3#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 8#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 8#5 3#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_3] using ob)
#print axioms site_3
#print axioms word_3
#print axioms step_3

theorem site_4 : EntryBinding.plan.code[4]? = some (6028, 2600893577) := rfl
theorem room_4 (initial : NativeState) : 4 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_4 : NativeEntryBodyDispatch.Madd64.selected 9#5 4#5 6#5 = 2600893577#32 := by decide
theorem step_4 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (4+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[4]'(room_4 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6028, 2600893577) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 6028 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (6028, 2600893577) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (4+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 4 + 4#64 = offset EntryBinding.plan (4+1) from by decide)
  have draws : DefaultState.drawsBefore initial 4 ≤ DefaultState.drawsBefore initial (4+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 4 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_4 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 9#5 4#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 9#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 9#5 4#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_4] using ob)
#print axioms site_4
#print axioms word_4
#print axioms step_4

theorem site_5 : EntryBinding.plan.code[5]? = some (6032, 2613476490) := rfl
theorem room_5 (initial : NativeState) : 5 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_5 : NativeEntryBodyDispatch.Umulh64.selected 10#5 4#5 6#5 = 2613476490#32 := by decide
theorem step_5 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (5+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[5]'(room_5 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6032, 2613476490) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 6032 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (6032, 2613476490) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (5+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 5 + 4#64 = offset EntryBinding.plan (5+1) from by decide)
  have draws : DefaultState.drawsBefore initial 5 ≤ DefaultState.drawsBefore initial (5+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 5 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_5 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 10#5 4#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 10#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 10#5 4#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_5] using ob)
#print axioms site_5
#print axioms word_5
#print axioms step_5

theorem site_6 : EntryBinding.plan.code[6]? = some (6036, 3942842500) := rfl
theorem room_6 (initial : NativeState) : 6 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_6 : NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5 = 3942842500#32 := by decide
theorem step_6 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 6 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (6+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[6]'(room_6 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6036, 3942842500) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 6036 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (6036, 3942842500) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (6+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 6 + 4#64 = offset EntryBinding.plan (6+1) from by decide)
  have draws : DefaultState.drawsBefore initial 6 ≤ DefaultState.drawsBefore initial (6+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 6 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_6 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_6] using ob)
#print axioms site_6
#print axioms word_6
#print axioms step_6

theorem site_7 : EntryBinding.plan.code[7]? = some (6040, 3666093188) := rfl
theorem room_7 (initial : NativeState) : 7 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_7 : N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5 = 3666093188#32 := by decide
theorem step_7 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 7 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (7+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[7]'(room_7 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6040, 3666093188) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 6040 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (6040, 3666093188) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (7+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 7 + 4#64 = offset EntryBinding.plan (7+1) from by decide)
  have draws : DefaultState.drawsBefore initial 7 ≤ DefaultState.drawsBefore initial (7+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 7 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_7 initial) compiles page (by decide)
    (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x inv
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_12 real x 4#5 4#5 4#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csneg_outputs x fin 4#5 4#5 4#5 vh, memory⟩)
    next (by simpa only [word_7] using ob)
#print axioms site_7
#print axioms word_7
#print axioms step_7

theorem site_8 : EntryBinding.plan.code[8]? = some (6044, 3667862512) := rfl
theorem room_8 (initial : NativeState) : 8 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_8 : NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5 = 3667862512#32 := by decide
theorem step_8 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 8 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (8+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[8]'(room_8 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6044, 3667862512) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 6044 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (6044, 3667862512) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (8+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 8 + 4#64 = offset EntryBinding.plan (8+1) from by decide)
  have draws : DefaultState.drawsBefore initial 8 ≤ DefaultState.drawsBefore initial (8+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 8 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_8 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_2 real x 16#5 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_8] using ob)
#print axioms site_8
#print axioms word_8
#print axioms step_8

theorem site_9 : EntryBinding.plan.code[9]? = some (6048, 2869428521) := rfl
theorem room_9 (initial : NativeState) : 9 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_9 : NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 8#5 = 2869428521#32 := by decide
theorem step_9 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 9 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (9+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[9]'(room_9 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6048, 2869428521) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 6048 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (6048, 2869428521) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (9+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 9 + 4#64 = offset EntryBinding.plan (9+1) from by decide)
  have draws : DefaultState.drawsBefore initial 9 ≤ DefaultState.drawsBefore initial (9+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 9 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_9 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 8#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 9#5 9#5 0#6 8#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_9] using ob)
#print axioms site_9
#print axioms word_9
#print axioms step_9

theorem site_10 : EntryBinding.plan.code[10]? = some (6052, 2585723210) := rfl
theorem room_10 (initial : NativeState) : 10 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_10 : NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5 = 2585723210#32 := by decide
theorem step_10 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 10 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (10+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[10]'(room_10 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6052, 2585723210) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 6052 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (6052, 2585723210) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (10+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 10 + 4#64 = offset EntryBinding.plan (10+1) from by decide)
  have draws : DefaultState.drawsBefore initial 10 ≤ DefaultState.drawsBefore initial (10+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 10 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_10 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 10#5 10#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_10] using ob)
#print axioms site_10
#print axioms word_10
#print axioms step_10

theorem site_11 : EntryBinding.plan.code[11]? = some (6056, 3943039139) := rfl
theorem room_11 (initial : NativeState) : 11 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_11 : NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5 = 3943039139#32 := by decide
theorem step_11 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 11 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (11+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[11]'(room_11 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6056, 3943039139) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 6056 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (6056, 3943039139) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (11+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 11 + 4#64 = offset EntryBinding.plan (11+1) from by decide)
  have draws : DefaultState.drawsBefore initial 11 ≤ DefaultState.drawsBefore initial (11+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 11 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_11 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_11] using ob)
#print axioms site_11
#print axioms word_11
#print axioms step_11

theorem site_12 : EntryBinding.plan.code[12]? = some (6060, 3666027619) := rfl
theorem room_12 (initial : NativeState) : 12 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_12 : N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5 = 3666027619#32 := by decide
theorem step_12 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 12 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (12+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[12]'(room_12 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6060, 3666027619) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 6060 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (6060, 3666027619) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (12+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 12 + 4#64 = offset EntryBinding.plan (12+1) from by decide)
  have draws : DefaultState.drawsBefore initial 12 ≤ DefaultState.drawsBefore initial (12+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 12 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_12 initial) compiles page (by decide)
    (N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 3#5 3#5 3#5) (none) x inv
    (N1D226.CsnegCs64Generic.Value.tailX real x 3#5 3#5 3#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_12 real x 3#5 3#5 3#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csneg_outputs x fin 3#5 3#5 3#5 vh, memory⟩)
    next (by simpa only [word_12] using ob)
#print axioms site_12
#print axioms word_12
#print axioms step_12

theorem site_13 : EntryBinding.plan.code[13]? = some (6064, 3666878992) := rfl
theorem room_13 (initial : NativeState) : 13 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_13 : N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5 = 3666878992#32 := by decide
theorem step_13 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 13 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (13+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[13]'(room_13 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6064, 3666878992) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 6064 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (6064, 3666878992) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (13+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 13 + 4#64 = offset EntryBinding.plan (13+1) from by decide)
  have draws : DefaultState.drawsBefore initial 13 ≤ DefaultState.drawsBefore initial (13+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 13 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_13 initial) compiles page (by decide)
    (N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 16#5 16#5 16#5) (none) x inv
    (N1D226.CsinvCs64Generic.Value.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_11 real x 16#5 16#5 16#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csinv_outputs x fin 16#5 16#5 16#5 vh, memory⟩)
    next (by simpa only [word_13] using ob)
#print axioms site_13
#print axioms word_13
#print axioms step_13

theorem site_14 : EntryBinding.plan.code[14]? = some (6068, 2600696975) := rfl
theorem room_14 (initial : NativeState) : 14 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_14 : NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5 = 2600696975#32 := by decide
theorem step_14 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 14 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (14+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[14]'(room_14 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6068, 2600696975) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 6068 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (6068, 2600696975) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (14+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 14 + 4#64 = offset EntryBinding.plan (14+1) from by decide)
  have draws : DefaultState.drawsBefore initial 14 ≤ DefaultState.drawsBefore initial (14+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 14 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_14 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 3)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_14] using ob)
#print axioms site_14
#print axioms word_14
#print axioms step_14

theorem site_15 : EntryBinding.plan.code[15]? = some (6072, 2613279875) := rfl
theorem room_15 (initial : NativeState) : 15 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_15 : NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5 = 2613279875#32 := by decide
theorem step_15 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 15 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (15+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[15]'(room_15 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6072, 2613279875) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_15
  have pc : x.regs._PC = MemReloc.imageAddress base 6072 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (6072, 2613279875) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (15+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 15 + 4#64 = offset EntryBinding.plan (15+1) from by decide)
  have draws : DefaultState.drawsBefore initial 15 ≤ DefaultState.drawsBefore initial (15+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 15 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_15 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 3)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_15] using ob)
#print axioms site_15
#print axioms word_15
#print axioms step_15

theorem site_16 : EntryBinding.plan.code[16]? = some (6076, 2869493992) := rfl
theorem room_16 (initial : NativeState) : 16 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_16 : NativeEntryBodyDispatch.AddsShift64.selected 8#5 7#5 0#6 9#5 = 2869493992#32 := by decide
theorem step_16 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 16 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (16+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[16]'(room_16 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6076, 2869493992) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 6076 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (6076, 2869493992) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (16+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 16 + 4#64 = offset EntryBinding.plan (16+1) from by decide)
  have draws : DefaultState.drawsBefore initial 16 ≤ DefaultState.drawsBefore initial (16+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 16 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_16 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 8#5 7#5 0#6 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 8#5 7#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 8#5 7#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_16] using ob)
#print axioms site_16
#print axioms word_16
#print axioms step_16

theorem site_17 : EntryBinding.plan.code[17]? = some (6080, 3121217833) := rfl
theorem room_17 (initial : NativeState) : 17 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_17 : NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 10#5 = 3121217833#32 := by decide
theorem step_17 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 17 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (17+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[17]'(room_17 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6080, 3121217833) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 6080 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (6080, 3121217833) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (17+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 17 + 4#64 = offset EntryBinding.plan (17+1) from by decide)
  have draws : DefaultState.drawsBefore initial 17 ≤ DefaultState.drawsBefore initial (17+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 17 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_17 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 9#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_17] using ob)
#print axioms site_17
#print axioms word_17
#print axioms step_17

theorem site_18 : EntryBinding.plan.code[18]? = some (6084, 2585723210) := rfl
theorem room_18 (initial : NativeState) : 18 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_18 : NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5 = 2585723210#32 := by decide
theorem step_18 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 18 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (18+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[18]'(room_18 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6084, 2585723210) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 6084 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (6084, 2585723210) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (18+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 18 + 4#64 = offset EntryBinding.plan (18+1) from by decide)
  have draws : DefaultState.drawsBefore initial 18 ≤ DefaultState.drawsBefore initial (18+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 18 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_18 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 10#5 10#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_18] using ob)
#print axioms site_18
#print axioms word_18
#print axioms step_18

theorem site_19 : EntryBinding.plan.code[19]? = some (6088, 2969568799) := rfl
theorem room_19 (initial : NativeState) : 19 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_19 : N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12 = 2969568799#32 := by decide
theorem step_19 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 19 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (19+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[19]'(room_19 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6088, 2969568799) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 6088 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (6088, 2969568799) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (19+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 19 + 4#64 = offset EntryBinding.plan (19+1) from by decide)
  have draws : DefaultState.drawsBefore initial 19 ≤ DefaultState.drawsBefore initial (19+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 19 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_19 initial) compiles page (by decide)
    (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ _ (fun s => s.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) (by rfl) x inv
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) (TranslateScalarTagCheck.Runtime.tail_10 real x 16#5 1#12 (by decide)) next (by simpa only [word_19] using ob)
#print axioms site_19
#print axioms word_19
#print axioms step_19

theorem site_20 : EntryBinding.plan.code[20]? = some (6092, 3390046703) := rfl
theorem room_20 (initial : NativeState) : 20 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_20 : NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5 = 3390046703#32 := by decide
theorem step_20 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 20 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (20+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[20]'(room_20 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6092, 3390046703) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 6092 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (6092, 3390046703) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (20+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 20 + 4#64 = offset EntryBinding.plan (20+1) from by decide)
  have draws : DefaultState.drawsBefore initial 20 ≤ DefaultState.drawsBefore initial (20+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 20 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_20 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_20] using ob)
#print axioms site_20
#print axioms word_20
#print axioms step_20

theorem site_21 : EntryBinding.plan.code[21]? = some (6096, 3121086952) := rfl
theorem room_21 (initial : NativeState) : 21 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_21 : NativeEntryBodyDispatch.Adcs64.selected 8#5 15#5 8#5 = 3121086952#32 := by decide
theorem step_21 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 21 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (21+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[21]'(room_21 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6096, 3121086952) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 6096 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (6096, 3121086952) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (21+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 21 + 4#64 = offset EntryBinding.plan (21+1) from by decide)
  have draws : DefaultState.drawsBefore initial 21 ≤ DefaultState.drawsBefore initial (21+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 21 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_21 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 8#5 15#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 8#5 15#5 8#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 8#5 15#5 8#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_21] using ob)
#print axioms site_21
#print axioms word_21
#print axioms step_21

theorem site_22 : EntryBinding.plan.code[22]? = some (6100, 3390046307) := rfl
theorem room_22 (initial : NativeState) : 22 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_22 : NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5 = 3390046307#32 := by decide
theorem step_22 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 22 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (22+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[22]'(room_22 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6100, 3390046307) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 6100 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (6100, 3390046307) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (22+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 22 + 4#64 = offset EntryBinding.plan (22+1) from by decide)
  have draws : DefaultState.drawsBefore initial 22 ≤ DefaultState.drawsBefore initial (22+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 22 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_22 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_22] using ob)
#print axioms site_22
#print axioms word_22
#print axioms step_22

theorem site_23 : EntryBinding.plan.code[23]? = some (6104, 3121152105) := rfl
theorem room_23 (initial : NativeState) : 23 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_23 : NativeEntryBodyDispatch.Adcs64.selected 9#5 3#5 9#5 = 3121152105#32 := by decide
theorem step_23 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 23 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (23+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[23]'(room_23 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6104, 3121152105) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 6104 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (6104, 3121152105) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (23+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 23 + 4#64 = offset EntryBinding.plan (23+1) from by decide)
  have draws : DefaultState.drawsBefore initial 23 ≤ DefaultState.drawsBefore initial (23+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 23 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_23 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 9#5 3#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 9#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 9#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_23] using ob)
#print axioms site_23
#print axioms word_23
#print axioms step_23

theorem site_24 : EntryBinding.plan.code[24]? = some (6108, 2584740170) := rfl
theorem room_24 (initial : NativeState) : 24 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_24 : NativeEntryBodyDispatch.Adc64.selected 10#5 10#5 16#5 = 2584740170#32 := by decide
theorem step_24 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 24 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (24+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[24]'(room_24 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6108, 2584740170) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 6108 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (6108, 2584740170) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (24+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 24 + 4#64 = offset EntryBinding.plan (24+1) from by decide)
  have draws : DefaultState.drawsBefore initial 24 ≤ DefaultState.drawsBefore initial (24+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 24 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_24 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 10#5 10#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 16), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_24] using ob)
#print axioms site_24
#print axioms word_24
#print axioms step_24

theorem site_27 : EntryBinding.plan.code[27]? = some (6120, 2600828011) := rfl
theorem room_27 (initial : NativeState) : 27 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_27 : NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 5#5 = 2600828011#32 := by decide
theorem step_27 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 27 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (27+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[27]'(room_27 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6120, 2600828011) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 6120 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (6120, 2600828011) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (27+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 27 + 4#64 = offset EntryBinding.plan (27+1) from by decide)
  have draws : DefaultState.drawsBefore initial 27 ≤ DefaultState.drawsBefore initial (27+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 27 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_27 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 11#5 3#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_27] using ob)
#print axioms site_27
#print axioms word_27
#print axioms step_27

theorem site_28 : EntryBinding.plan.code[28]? = some (6124, 2613410924) := rfl
theorem room_28 (initial : NativeState) : 28 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_28 : NativeEntryBodyDispatch.Umulh64.selected 12#5 3#5 5#5 = 2613410924#32 := by decide
theorem step_28 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 28 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (28+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[28]'(room_28 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6124, 2613410924) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_28
  have pc : x.regs._PC = MemReloc.imageAddress base 6124 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    28 x inv.core (6124, 2613410924) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (28+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 28 + 4#64 = offset EntryBinding.plan (28+1) from by decide)
  have draws : DefaultState.drawsBefore initial 28 ≤ DefaultState.drawsBefore initial (28+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 28 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_28 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 12#5 3#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 12#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 12#5 3#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_28] using ob)
#print axioms site_28
#print axioms word_28
#print axioms step_28

theorem site_29 : EntryBinding.plan.code[29]? = some (6128, 2600893581) := rfl
theorem room_29 (initial : NativeState) : 29 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_29 : NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 6#5 = 2600893581#32 := by decide
theorem step_29 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 29 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (29+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[29]'(room_29 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6128, 2600893581) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_29
  have pc : x.regs._PC = MemReloc.imageAddress base 6128 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    29 x inv.core (6128, 2600893581) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (29+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 29 + 4#64 = offset EntryBinding.plan (29+1) from by decide)
  have draws : DefaultState.drawsBefore initial 29 ≤ DefaultState.drawsBefore initial (29+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 29 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_29 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 13#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 13#5 4#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_29] using ob)
#print axioms site_29
#print axioms word_29
#print axioms step_29

theorem site_30 : EntryBinding.plan.code[30]? = some (6132, 2613476494) := rfl
theorem room_30 (initial : NativeState) : 30 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_30 : NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 6#5 = 2613476494#32 := by decide
theorem step_30 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 30 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (30+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[30]'(room_30 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6132, 2613476494) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_30
  have pc : x.regs._PC = MemReloc.imageAddress base 6132 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    30 x inv.core (6132, 2613476494) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (30+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 30 + 4#64 = offset EntryBinding.plan (30+1) from by decide)
  have draws : DefaultState.drawsBefore initial 30 ≤ DefaultState.drawsBefore initial (30+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 30 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_30 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 14#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 14#5 4#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_30] using ob)
#print axioms site_30
#print axioms word_30
#print axioms step_30

theorem site_31 : EntryBinding.plan.code[31]? = some (6136, 3942842500) := rfl
theorem room_31 (initial : NativeState) : 31 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_31 : NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5 = 3942842500#32 := by decide
theorem step_31 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 31 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (31+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[31]'(room_31 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6136, 3942842500) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_31
  have pc : x.regs._PC = MemReloc.imageAddress base 6136 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    31 x inv.core (6136, 3942842500) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (31+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 31 + 4#64 = offset EntryBinding.plan (31+1) from by decide)
  have draws : DefaultState.drawsBefore initial 31 ≤ DefaultState.drawsBefore initial (31+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 31 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_31 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_31] using ob)
#print axioms site_31
#print axioms word_31
#print axioms step_31

theorem site_32 : EntryBinding.plan.code[32]? = some (6140, 3666093188) := rfl
theorem room_32 (initial : NativeState) : 32 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_32 : N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5 = 3666093188#32 := by decide
theorem step_32 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 32 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (32+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[32]'(room_32 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6140, 3666093188) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_32
  have pc : x.regs._PC = MemReloc.imageAddress base 6140 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    32 x inv.core (6140, 3666093188) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (32+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 32 + 4#64 = offset EntryBinding.plan (32+1) from by decide)
  have draws : DefaultState.drawsBefore initial 32 ≤ DefaultState.drawsBefore initial (32+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 32 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_32 initial) compiles page (by decide)
    (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x inv
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_12 real x 4#5 4#5 4#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csneg_outputs x fin 4#5 4#5 4#5 vh, memory⟩)
    next (by simpa only [word_32] using ob)
#print axioms site_32
#print axioms word_32
#print axioms step_32

theorem site_33 : EntryBinding.plan.code[33]? = some (6144, 3667862512) := rfl
theorem room_33 (initial : NativeState) : 33 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_33 : NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5 = 3667862512#32 := by decide
theorem step_33 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 33 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (33+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[33]'(room_33 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6144, 3667862512) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_33
  have pc : x.regs._PC = MemReloc.imageAddress base 6144 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    33 x inv.core (6144, 3667862512) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (33+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 33 + 4#64 = offset EntryBinding.plan (33+1) from by decide)
  have draws : DefaultState.drawsBefore initial 33 ≤ DefaultState.drawsBefore initial (33+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 33 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_33 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_2 real x 16#5 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_33] using ob)
#print axioms site_33
#print axioms word_33
#print axioms step_33

theorem site_34 : EntryBinding.plan.code[34]? = some (6148, 2869690797) := rfl
theorem room_34 (initial : NativeState) : 34 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_34 : NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 12#5 = 2869690797#32 := by decide
theorem step_34 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 34 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (34+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[34]'(room_34 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6148, 2869690797) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_34
  have pc : x.regs._PC = MemReloc.imageAddress base 6148 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    34 x inv.core (6148, 2869690797) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (34+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 34 + 4#64 = offset EntryBinding.plan (34+1) from by decide)
  have draws : DefaultState.drawsBefore initial 34 ≤ DefaultState.drawsBefore initial (34+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 34 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_34 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 13#5 13#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_34] using ob)
#print axioms site_34
#print axioms word_34
#print axioms step_34

theorem site_35 : EntryBinding.plan.code[35]? = some (6152, 2585723342) := rfl
theorem room_35 (initial : NativeState) : 35 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_35 : NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5 = 2585723342#32 := by decide
theorem step_35 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 35 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (35+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[35]'(room_35 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6152, 2585723342) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_35
  have pc : x.regs._PC = MemReloc.imageAddress base 6152 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    35 x inv.core (6152, 2585723342) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (35+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 35 + 4#64 = offset EntryBinding.plan (35+1) from by decide)
  have draws : DefaultState.drawsBefore initial 35 ≤ DefaultState.drawsBefore initial (35+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 35 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_35 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_35] using ob)
#print axioms site_35
#print axioms word_35
#print axioms step_35

theorem site_36 : EntryBinding.plan.code[36]? = some (6156, 3943039139) := rfl
theorem room_36 (initial : NativeState) : 36 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_36 : NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5 = 3943039139#32 := by decide
theorem step_36 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 36 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (36+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[36]'(room_36 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6156, 3943039139) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_36
  have pc : x.regs._PC = MemReloc.imageAddress base 6156 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    36 x inv.core (6156, 3943039139) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (36+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 36 + 4#64 = offset EntryBinding.plan (36+1) from by decide)
  have draws : DefaultState.drawsBefore initial 36 ≤ DefaultState.drawsBefore initial (36+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 36 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_36 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_36] using ob)
#print axioms site_36
#print axioms word_36
#print axioms step_36

theorem site_37 : EntryBinding.plan.code[37]? = some (6160, 3666027619) := rfl
theorem room_37 (initial : NativeState) : 37 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_37 : N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5 = 3666027619#32 := by decide
theorem step_37 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 37 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (37+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[37]'(room_37 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6160, 3666027619) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_37
  have pc : x.regs._PC = MemReloc.imageAddress base 6160 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    37 x inv.core (6160, 3666027619) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (37+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 37 + 4#64 = offset EntryBinding.plan (37+1) from by decide)
  have draws : DefaultState.drawsBefore initial 37 ≤ DefaultState.drawsBefore initial (37+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 37 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_37 initial) compiles page (by decide)
    (N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 3#5 3#5 3#5) (none) x inv
    (N1D226.CsnegCs64Generic.Value.tailX real x 3#5 3#5 3#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_12 real x 3#5 3#5 3#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csneg_outputs x fin 3#5 3#5 3#5 vh, memory⟩)
    next (by simpa only [word_37] using ob)
#print axioms site_37
#print axioms word_37
#print axioms step_37

theorem site_38 : EntryBinding.plan.code[38]? = some (6164, 3666878992) := rfl
theorem room_38 (initial : NativeState) : 38 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_38 : N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5 = 3666878992#32 := by decide
theorem step_38 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 38 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (38+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[38]'(room_38 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6164, 3666878992) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_38
  have pc : x.regs._PC = MemReloc.imageAddress base 6164 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    38 x inv.core (6164, 3666878992) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (38+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 38 + 4#64 = offset EntryBinding.plan (38+1) from by decide)
  have draws : DefaultState.drawsBefore initial 38 ≤ DefaultState.drawsBefore initial (38+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 38 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_38 initial) compiles page (by decide)
    (N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 16#5 16#5 16#5) (none) x inv
    (N1D226.CsinvCs64Generic.Value.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_11 real x 16#5 16#5 16#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csinv_outputs x fin 16#5 16#5 16#5 vh, memory⟩)
    next (by simpa only [word_38] using ob)
#print axioms site_38
#print axioms word_38
#print axioms step_38

theorem site_39 : EntryBinding.plan.code[39]? = some (6168, 2600696975) := rfl
theorem room_39 (initial : NativeState) : 39 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_39 : NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5 = 2600696975#32 := by decide
theorem step_39 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 39 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (39+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[39]'(room_39 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6168, 2600696975) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_39
  have pc : x.regs._PC = MemReloc.imageAddress base 6168 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    39 x inv.core (6168, 2600696975) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (39+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 39 + 4#64 = offset EntryBinding.plan (39+1) from by decide)
  have draws : DefaultState.drawsBefore initial 39 ≤ DefaultState.drawsBefore initial (39+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 39 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_39 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 3)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_39] using ob)
#print axioms site_39
#print axioms word_39
#print axioms step_39

theorem site_40 : EntryBinding.plan.code[40]? = some (6172, 2613279875) := rfl
theorem room_40 (initial : NativeState) : 40 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_40 : NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5 = 2613279875#32 := by decide
theorem step_40 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 40 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (40+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[40]'(room_40 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6172, 2613279875) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_40
  have pc : x.regs._PC = MemReloc.imageAddress base 6172 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    40 x inv.core (6172, 2613279875) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (40+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 40 + 4#64 = offset EntryBinding.plan (40+1) from by decide)
  have draws : DefaultState.drawsBefore initial 40 ≤ DefaultState.drawsBefore initial (40+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 40 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_40 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 3)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_40] using ob)
#print axioms site_40
#print axioms word_40
#print axioms step_40

theorem site_41 : EntryBinding.plan.code[41]? = some (6176, 2869756268) := rfl
theorem room_41 (initial : NativeState) : 41 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_41 : NativeEntryBodyDispatch.AddsShift64.selected 12#5 11#5 0#6 13#5 = 2869756268#32 := by decide
theorem step_41 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 41 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (41+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[41]'(room_41 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6176, 2869756268) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_41
  have pc : x.regs._PC = MemReloc.imageAddress base 6176 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    41 x inv.core (6176, 2869756268) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (41+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 41 + 4#64 = offset EntryBinding.plan (41+1) from by decide)
  have draws : DefaultState.drawsBefore initial 41 ≤ DefaultState.drawsBefore initial (41+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 41 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_41 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 12#5 11#5 0#6 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 12#5 11#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 12#5 11#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_41] using ob)
#print axioms site_41
#print axioms word_41
#print axioms step_41

theorem site_42 : EntryBinding.plan.code[42]? = some (6180, 3121480109) := rfl
theorem room_42 (initial : NativeState) : 42 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_42 : NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 14#5 = 3121480109#32 := by decide
theorem step_42 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 42 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (42+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[42]'(room_42 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6180, 3121480109) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_42
  have pc : x.regs._PC = MemReloc.imageAddress base 6180 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    42 x inv.core (6180, 3121480109) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (42+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 42 + 4#64 = offset EntryBinding.plan (42+1) from by decide)
  have draws : DefaultState.drawsBefore initial 42 ≤ DefaultState.drawsBefore initial (42+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 42 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_42 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 14#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 13#5 13#5 14#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_42] using ob)
#print axioms site_42
#print axioms word_42
#print axioms step_42

theorem site_43 : EntryBinding.plan.code[43]? = some (6184, 2585723342) := rfl
theorem room_43 (initial : NativeState) : 43 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_43 : NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5 = 2585723342#32 := by decide
theorem step_43 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 43 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (43+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[43]'(room_43 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6184, 2585723342) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_43
  have pc : x.regs._PC = MemReloc.imageAddress base 6184 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    43 x inv.core (6184, 2585723342) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (43+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 43 + 4#64 = offset EntryBinding.plan (43+1) from by decide)
  have draws : DefaultState.drawsBefore initial 43 ≤ DefaultState.drawsBefore initial (43+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 43 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_43 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_43] using ob)
#print axioms site_43
#print axioms word_43
#print axioms step_43

theorem site_44 : EntryBinding.plan.code[44]? = some (6188, 2969568799) := rfl
theorem room_44 (initial : NativeState) : 44 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_44 : N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12 = 2969568799#32 := by decide
theorem step_44 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 44 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (44+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[44]'(room_44 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6188, 2969568799) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_44
  have pc : x.regs._PC = MemReloc.imageAddress base 6188 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    44 x inv.core (6188, 2969568799) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (44+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 44 + 4#64 = offset EntryBinding.plan (44+1) from by decide)
  have draws : DefaultState.drawsBefore initial 44 ≤ DefaultState.drawsBefore initial (44+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 44 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_44 initial) compiles page (by decide)
    (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ _ (fun s => s.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) (by rfl) x inv
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) (TranslateScalarTagCheck.Runtime.tail_10 real x 16#5 1#12 (by decide)) next (by simpa only [word_44] using ob)
#print axioms site_44
#print axioms word_44
#print axioms step_44

theorem site_45 : EntryBinding.plan.code[45]? = some (6192, 3390046703) := rfl
theorem room_45 (initial : NativeState) : 45 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_45 : NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5 = 3390046703#32 := by decide
theorem step_45 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 45 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (45+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[45]'(room_45 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6192, 3390046703) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_45
  have pc : x.regs._PC = MemReloc.imageAddress base 6192 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    45 x inv.core (6192, 3390046703) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (45+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 45 + 4#64 = offset EntryBinding.plan (45+1) from by decide)
  have draws : DefaultState.drawsBefore initial 45 ≤ DefaultState.drawsBefore initial (45+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 45 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_45 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_45] using ob)
#print axioms site_45
#print axioms word_45
#print axioms step_45

theorem site_46 : EntryBinding.plan.code[46]? = some (6196, 3121349100) := rfl
theorem room_46 (initial : NativeState) : 46 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_46 : NativeEntryBodyDispatch.Adcs64.selected 12#5 15#5 12#5 = 3121349100#32 := by decide
theorem step_46 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 46 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (46+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[46]'(room_46 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6196, 3121349100) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_46
  have pc : x.regs._PC = MemReloc.imageAddress base 6196 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    46 x inv.core (6196, 3121349100) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (46+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 46 + 4#64 = offset EntryBinding.plan (46+1) from by decide)
  have draws : DefaultState.drawsBefore initial 46 ≤ DefaultState.drawsBefore initial (46+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 46 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_46 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 12#5 15#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 12#5 15#5 12#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 12#5 15#5 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_46] using ob)
#print axioms site_46
#print axioms word_46
#print axioms step_46

theorem site_47 : EntryBinding.plan.code[47]? = some (6200, 3390046307) := rfl
theorem room_47 (initial : NativeState) : 47 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_47 : NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5 = 3390046307#32 := by decide
theorem step_47 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 47 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (47+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[47]'(room_47 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6200, 3390046307) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_47
  have pc : x.regs._PC = MemReloc.imageAddress base 6200 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    47 x inv.core (6200, 3390046307) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (47+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 47 + 4#64 = offset EntryBinding.plan (47+1) from by decide)
  have draws : DefaultState.drawsBefore initial 47 ≤ DefaultState.drawsBefore initial (47+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 47 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_47 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_47] using ob)
#print axioms site_47
#print axioms word_47
#print axioms step_47

theorem site_48 : EntryBinding.plan.code[48]? = some (6204, 3121414253) := rfl
theorem room_48 (initial : NativeState) : 48 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_48 : NativeEntryBodyDispatch.Adcs64.selected 13#5 3#5 13#5 = 3121414253#32 := by decide
theorem step_48 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 48 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (48+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[48]'(room_48 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6204, 3121414253) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_48
  have pc : x.regs._PC = MemReloc.imageAddress base 6204 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    48 x inv.core (6204, 3121414253) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (48+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 48 + 4#64 = offset EntryBinding.plan (48+1) from by decide)
  have draws : DefaultState.drawsBefore initial 48 ≤ DefaultState.drawsBefore initial (48+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 48 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_48 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 13#5 3#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_48] using ob)
#print axioms site_48
#print axioms word_48
#print axioms step_48

theorem site_49 : EntryBinding.plan.code[49]? = some (6208, 2584740302) := rfl
theorem room_49 (initial : NativeState) : 49 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_49 : NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5 = 2584740302#32 := by decide
theorem step_49 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 49 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (49+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[49]'(room_49 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6208, 2584740302) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_49
  have pc : x.regs._PC = MemReloc.imageAddress base 6208 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    49 x inv.core (6208, 2584740302) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (49+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 49 + 4#64 = offset EntryBinding.plan (49+1) from by decide)
  have draws : DefaultState.drawsBefore initial 49 ≤ DefaultState.drawsBefore initial (49+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 49 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_49 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 16), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_49] using ob)
#print axioms site_49
#print axioms word_49
#print axioms step_49

theorem site_52 : EntryBinding.plan.code[52]? = some (6220, 3943628899) := rfl
theorem room_52 (initial : NativeState) : 52 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_52 : NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 15#5 = 3943628899#32 := by decide
theorem step_52 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 52 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (52+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[52]'(room_52 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6220, 3943628899) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_52
  have pc : x.regs._PC = MemReloc.imageAddress base 6220 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    52 x inv.core (6220, 3943628899) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (52+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 52 + 4#64 = offset EntryBinding.plan (52+1) from by decide)
  have draws : DefaultState.drawsBefore initial 52 ≤ DefaultState.drawsBefore initial (52+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 52 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_52 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_52] using ob)
#print axioms site_52
#print axioms word_52
#print axioms step_52

theorem site_53 : EntryBinding.plan.code[53]? = some (6224, 4195352708) := rfl
theorem room_53 (initial : NativeState) : 53 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_53 : NativeEntryBodyDispatch.Sbcs64Reg.selected 4#5 4#5 16#5 = 4195352708#32 := by decide
theorem step_53 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 53 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (53+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[53]'(room_53 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6224, 4195352708) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_53
  have pc : x.regs._PC = MemReloc.imageAddress base 6224 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    53 x inv.core (6224, 4195352708) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (53+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 53 + 4#64 = offset EntryBinding.plan (53+1) from by decide)
  have draws : DefaultState.drawsBefore initial 53 ≤ DefaultState.drawsBefore initial (53+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 53 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_53 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64Reg.selected 4#5 4#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64Reg.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_0 real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_53] using ob)
#print axioms site_53
#print axioms word_53
#print axioms step_53

theorem site_54 : EntryBinding.plan.code[54]? = some (6228, 3667862512) := rfl
theorem room_54 (initial : NativeState) : 54 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_54 : NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5 = 3667862512#32 := by decide
theorem step_54 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 54 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (54+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[54]'(room_54 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6228, 3667862512) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_54
  have pc : x.regs._PC = MemReloc.imageAddress base 6228 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    54 x inv.core (6228, 3667862512) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (54+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 54 + 4#64 = offset EntryBinding.plan (54+1) from by decide)
  have draws : DefaultState.drawsBefore initial 54 ≤ DefaultState.drawsBefore initial (54+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 54 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_54 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_2 real x 16#5 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_54] using ob)
#print axioms site_54
#print axioms word_54
#print axioms step_54

theorem site_56 : EntryBinding.plan.code[56]? = some (6236, 3942973925) := rfl
theorem room_56 (initial : NativeState) : 56 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_56 : NativeEntryBodyDispatch.SubsShift64.selected 5#5 15#5 0#6 5#5 = 3942973925#32 := by decide
theorem step_56 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 56 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (56+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[56]'(room_56 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6236, 3942973925) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_56
  have pc : x.regs._PC = MemReloc.imageAddress base 6236 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    56 x inv.core (6236, 3942973925) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (56+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 56 + 4#64 = offset EntryBinding.plan (56+1) from by decide)
  have draws : DefaultState.drawsBefore initial 56 ≤ DefaultState.drawsBefore initial (56+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 56 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_56 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 5#5 15#5 0#6 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 5#5 15#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 5#5 15#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_56] using ob)
#print axioms site_56
#print axioms word_56
#print axioms step_56

theorem site_57 : EntryBinding.plan.code[57]? = some (6240, 4194697766) := rfl
theorem room_57 (initial : NativeState) : 57 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_57 : NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 17#5 6#5 = 4194697766#32 := by decide
theorem step_57 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 57 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (57+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[57]'(room_57 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6240, 4194697766) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_57
  have pc : x.regs._PC = MemReloc.imageAddress base 6240 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    57 x inv.core (6240, 4194697766) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (57+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 57 + 4#64 = offset EntryBinding.plan (57+1) from by decide)
  have draws : DefaultState.drawsBefore initial 57 ≤ DefaultState.drawsBefore initial (57+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 57 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_57 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 17#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 17), .reg (.x 6), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 17), .reg (.x 6), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64Reg.tailX real x 6#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_0 real x 6#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_57] using ob)
#print axioms site_57
#print axioms word_57
#print axioms step_57

theorem site_58 : EntryBinding.plan.code[58]? = some (6244, 3667862513) := rfl
theorem room_58 (initial : NativeState) : 58 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_58 : NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 17#5 = 3667862513#32 := by decide
theorem step_58 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 58 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (58+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[58]'(room_58 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6244, 3667862513) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_58
  have pc : x.regs._PC = MemReloc.imageAddress base 6244 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    58 x inv.core (6244, 3667862513) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (58+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 58 + 4#64 = offset EntryBinding.plan (58+1) from by decide)
  have draws : DefaultState.drawsBefore initial 58 ≤ DefaultState.drawsBefore initial (58+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 58 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_58 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 17), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 17#5 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_2 real x 17#5 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_58] using ob)
#print axioms site_58
#print axioms word_58
#print axioms step_58

theorem site_59 : EntryBinding.plan.code[59]? = some (6248, 3390046307) := rfl
theorem room_59 (initial : NativeState) : 59 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_59 : NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5 = 3390046307#32 := by decide
theorem step_59 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 59 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (59+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[59]'(room_59 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6248, 3390046307) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_59
  have pc : x.regs._PC = MemReloc.imageAddress base 6248 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    59 x inv.core (6248, 3390046307) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (59+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 59 + 4#64 = offset EntryBinding.plan (59+1) from by decide)
  have draws : DefaultState.drawsBefore initial 59 ≤ DefaultState.drawsBefore initial (59+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 59 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_59 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_59] using ob)
#print axioms site_59
#print axioms word_59
#print axioms step_59

theorem site_60 : EntryBinding.plan.code[60]? = some (6252, 3943694435) := rfl
theorem room_60 (initial : NativeState) : 60 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_60 : NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 16#5 = 3943694435#32 := by decide
theorem step_60 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 60 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (60+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[60]'(room_60 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6252, 3943694435) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_60
  have pc : x.regs._PC = MemReloc.imageAddress base 6252 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    60 x inv.core (6252, 3943694435) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (60+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 60 + 4#64 = offset EntryBinding.plan (60+1) from by decide)
  have draws : DefaultState.drawsBefore initial 60 ≤ DefaultState.drawsBefore initial (60+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 60 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_60 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 3#5 3#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_60] using ob)
#print axioms site_60
#print axioms word_60
#print axioms step_60

theorem site_61 : EntryBinding.plan.code[61]? = some (6256, 3390046340) := rfl
theorem room_61 (initial : NativeState) : 61 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_61 : NativeEntryBodyDispatch.SecpEor64.selected 4#5 4#5 16#5 = 3390046340#32 := by decide
theorem step_61 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 61 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (61+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[61]'(room_61 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6256, 3390046340) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_61
  have pc : x.regs._PC = MemReloc.imageAddress base 6256 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    61 x inv.core (6256, 3390046340) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (61+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 61 + 4#64 = offset EntryBinding.plan (61+1) from by decide)
  have draws : DefaultState.drawsBefore initial 61 ≤ DefaultState.drawsBefore initial (61+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 61 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_61 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 4#5 4#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.eor, [.reg (.x 4), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_61] using ob)
#print axioms site_61
#print axioms word_61
#print axioms step_61

theorem site_62 : EntryBinding.plan.code[62]? = some (6260, 3658481796) := rfl
theorem room_62 (initial : NativeState) : 62 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_62 : NativeEntryBodyDispatch.SecpSbc64.selected 4#5 4#5 16#5 = 3658481796#32 := by decide
theorem step_62 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 62 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (62+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[62]'(room_62 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6260, 3658481796) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_62
  have pc : x.regs._PC = MemReloc.imageAddress base 6260 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    62 x inv.core (6260, 3658481796) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (62+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 62 + 4#64 = offset EntryBinding.plan (62+1) from by decide)
  have draws : DefaultState.drawsBefore initial 62 ≤ DefaultState.drawsBefore initial (62+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 62 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_62 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpSbc64.selected 4#5 4#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpSbc64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_14 real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_62] using ob)
#print axioms site_62
#print axioms word_62
#print axioms step_62

theorem site_63 : EntryBinding.plan.code[63]? = some (6264, 3390111909) := rfl
theorem room_63 (initial : NativeState) : 63 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_63 : NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 17#5 = 3390111909#32 := by decide
theorem step_63 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 63 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (63+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[63]'(room_63 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6264, 3390111909) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_63
  have pc : x.regs._PC = MemReloc.imageAddress base 6264 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    63 x inv.core (6264, 3390111909) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (63+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 63 + 4#64 = offset EntryBinding.plan (63+1) from by decide)
  have draws : DefaultState.drawsBefore initial 63 ≤ DefaultState.drawsBefore initial (63+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 63 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_63 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.eor, [.reg (.x 5), .reg (.x 17)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 5#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 5#5 5#5 17#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_63] using ob)
#print axioms site_63
#print axioms word_63
#print axioms step_63

theorem site_64 : EntryBinding.plan.code[64]? = some (6268, 3943760037) := rfl
theorem room_64 (initial : NativeState) : 64 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_64 : NativeEntryBodyDispatch.SubsShift64.selected 5#5 5#5 0#6 17#5 = 3943760037#32 := by decide
theorem step_64 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 64 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (64+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[64]'(room_64 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6268, 3943760037) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_64
  have pc : x.regs._PC = MemReloc.imageAddress base 6268 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    64 x inv.core (6268, 3943760037) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (64+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 64 + 4#64 = offset EntryBinding.plan (64+1) from by decide)
  have draws : DefaultState.drawsBefore initial 64 ≤ DefaultState.drawsBefore initial (64+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 64 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_64 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 5#5 5#5 0#6 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 5#5 5#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 5#5 5#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_64] using ob)
#print axioms site_64
#print axioms word_64
#print axioms step_64

theorem site_65 : EntryBinding.plan.code[65]? = some (6272, 3390111942) := rfl
theorem room_65 (initial : NativeState) : 65 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_65 : NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 17#5 = 3390111942#32 := by decide
theorem step_65 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 65 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (65+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[65]'(room_65 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6272, 3390111942) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_65
  have pc : x.regs._PC = MemReloc.imageAddress base 6272 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    65 x inv.core (6272, 3390111942) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (65+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 65 + 4#64 = offset EntryBinding.plan (65+1) from by decide)
  have draws : DefaultState.drawsBefore initial 65 ≤ DefaultState.drawsBefore initial (65+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 65 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_65 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.eor, [.reg (.x 6), .reg (.x 17)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_65] using ob)
#print axioms site_65
#print axioms word_65
#print axioms step_65

theorem site_66 : EntryBinding.plan.code[66]? = some (6276, 3658547398) := rfl
theorem room_66 (initial : NativeState) : 66 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_66 : NativeEntryBodyDispatch.SecpSbc64.selected 6#5 6#5 17#5 = 3658547398#32 := by decide
theorem step_66 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 66 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (66+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[66]'(room_66 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6276, 3658547398) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_66
  have pc : x.regs._PC = MemReloc.imageAddress base 6276 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    66 x inv.core (6276, 3658547398) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (66+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 66 + 4#64 = offset EntryBinding.plan (66+1) from by decide)
  have draws : DefaultState.drawsBefore initial 66 ≤ DefaultState.drawsBefore initial (66+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 66 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_66 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpSbc64.selected 6#5 6#5 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .reg (.x 17), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpSbc64.tailX real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_14 real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_66] using ob)
#print axioms site_66
#print axioms word_66
#print axioms step_66

theorem site_67 : EntryBinding.plan.code[67]? = some (6280, 3390046768) := rfl
theorem room_67 (initial : NativeState) : 67 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_67 : NativeEntryBodyDispatch.SecpEor64.selected 16#5 17#5 16#5 = 3390046768#32 := by decide
theorem step_67 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 67 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (67+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[67]'(room_67 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6280, 3390046768) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_67
  have pc : x.regs._PC = MemReloc.imageAddress base 6280 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    67 x inv.core (6280, 3390046768) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (67+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 67 + 4#64 = offset EntryBinding.plan (67+1) from by decide)
  have draws : DefaultState.drawsBefore initial 67 ≤ DefaultState.drawsBefore initial (67+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 67 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_67 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 16#5 17#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨.eor, [.reg (.x 17), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 16#5 17#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 16#5 17#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_67] using ob)
#print axioms site_67
#print axioms word_67
#print axioms step_67

theorem site_68 : EntryBinding.plan.code[68]? = some (6284, 2869494123) := rfl
theorem room_68 (initial : NativeState) : 68 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_68 : NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 9#5 = 2869494123#32 := by decide
theorem step_68 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 68 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (68+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[68]'(room_68 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6284, 2869494123) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_68
  have pc : x.regs._PC = MemReloc.imageAddress base 6284 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    68 x inv.core (6284, 2869494123) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (68+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 68 + 4#64 = offset EntryBinding.plan (68+1) from by decide)
  have draws : DefaultState.drawsBefore initial 68 ≤ DefaultState.drawsBefore initial (68+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 68 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_68 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 11#5 11#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 11#5 11#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_68] using ob)
#print axioms site_68
#print axioms word_68
#print axioms step_68

theorem site_69 : EntryBinding.plan.code[69]? = some (6288, 3121217932) := rfl
theorem room_69 (initial : NativeState) : 69 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_69 : NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 10#5 = 3121217932#32 := by decide
theorem step_69 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 69 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (69+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[69]'(room_69 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6288, 3121217932) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_69
  have pc : x.regs._PC = MemReloc.imageAddress base 6288 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    69 x inv.core (6288, 3121217932) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (69+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 69 + 4#64 = offset EntryBinding.plan (69+1) from by decide)
  have draws : DefaultState.drawsBefore initial 69 ≤ DefaultState.drawsBefore initial (69+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 69 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_69 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 10#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 12#5 12#5 10#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_69] using ob)
#print axioms site_69
#print axioms word_69
#print axioms step_69

theorem site_70 : EntryBinding.plan.code[70]? = some (6292, 3122594221) := rfl
theorem room_70 (initial : NativeState) : 70 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_70 : NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5 = 3122594221#32 := by decide
theorem step_70 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 70 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (70+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[70]'(room_70 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6292, 3122594221) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_70
  have pc : x.regs._PC = MemReloc.imageAddress base 6292 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    70 x inv.core (6292, 3122594221) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (70+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 70 + 4#64 = offset EntryBinding.plan (70+1) from by decide)
  have draws : DefaultState.drawsBefore initial 70 ≤ DefaultState.drawsBefore initial (70+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 70 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_70 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 13#5 13#5 (by decide) (by decide) (by decide)) next (by simpa only [word_70] using ob)
#print axioms site_70
#print axioms word_70
#print axioms step_70

theorem site_71 : EntryBinding.plan.code[71]? = some (6296, 2585723342) := rfl
theorem room_71 (initial : NativeState) : 71 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_71 : NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5 = 2585723342#32 := by decide
theorem step_71 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 71 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (71+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[71]'(room_71 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6296, 2585723342) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_71
  have pc : x.regs._PC = MemReloc.imageAddress base 6296 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    71 x inv.core (6296, 2585723342) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (71+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 71 + 4#64 = offset EntryBinding.plan (71+1) from by decide)
  have draws : DefaultState.drawsBefore initial 71 ≤ DefaultState.drawsBefore initial (71+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 71 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_71 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_71] using ob)
#print axioms site_71
#print axioms word_71
#print axioms step_71

theorem site_72 : EntryBinding.plan.code[72]? = some (6300, 2600828002) := rfl
theorem room_72 (initial : NativeState) : 72 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_72 : NativeEntryBodyDispatch.Madd64.selected 2#5 3#5 5#5 = 2600828002#32 := by decide
theorem step_72 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 72 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (72+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[72]'(room_72 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6300, 2600828002) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_72
  have pc : x.regs._PC = MemReloc.imageAddress base 6300 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    72 x inv.core (6300, 2600828002) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (72+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 72 + 4#64 = offset EntryBinding.plan (72+1) from by decide)
  have draws : DefaultState.drawsBefore initial 72 ≤ DefaultState.drawsBefore initial (72+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 72 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_72 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 2#5 3#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 2#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 2#5 3#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_72] using ob)
#print axioms site_72
#print axioms word_72
#print axioms step_72

theorem site_73 : EntryBinding.plan.code[73]? = some (6304, 2613410929) := rfl
theorem room_73 (initial : NativeState) : 73 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_73 : NativeEntryBodyDispatch.Umulh64.selected 17#5 3#5 5#5 = 2613410929#32 := by decide
theorem step_73 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 73 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (73+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[73]'(room_73 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6304, 2613410929) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_73
  have pc : x.regs._PC = MemReloc.imageAddress base 6304 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    73 x inv.core (6304, 2613410929) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (73+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 73 + 4#64 = offset EntryBinding.plan (73+1) from by decide)
  have draws : DefaultState.drawsBefore initial 73 ≤ DefaultState.drawsBefore initial (73+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 73 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_73 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 17#5 3#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 17), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 17#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 17#5 3#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_73] using ob)
#print axioms site_73
#print axioms word_73
#print axioms step_73

theorem site_74 : EntryBinding.plan.code[74]? = some (6308, 2600893583) := rfl
theorem room_74 (initial : NativeState) : 74 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_74 : NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 6#5 = 2600893583#32 := by decide
theorem step_74 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 74 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (74+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[74]'(room_74 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6308, 2600893583) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_74
  have pc : x.regs._PC = MemReloc.imageAddress base 6308 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    74 x inv.core (6308, 2600893583) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (74+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 74 + 4#64 = offset EntryBinding.plan (74+1) from by decide)
  have draws : DefaultState.drawsBefore initial 74 ≤ DefaultState.drawsBefore initial (74+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 74 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_74 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 15#5 4#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_74] using ob)
#print axioms site_74
#print axioms word_74
#print axioms step_74

theorem site_75 : EntryBinding.plan.code[75]? = some (6312, 2613476481) := rfl
theorem room_75 (initial : NativeState) : 75 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_75 : NativeEntryBodyDispatch.Umulh64.selected 1#5 4#5 6#5 = 2613476481#32 := by decide
theorem step_75 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 75 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (75+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[75]'(room_75 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6312, 2613476481) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_75
  have pc : x.regs._PC = MemReloc.imageAddress base 6312 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    75 x inv.core (6312, 2613476481) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (75+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 75 + 4#64 = offset EntryBinding.plan (75+1) from by decide)
  have draws : DefaultState.drawsBefore initial 75 ≤ DefaultState.drawsBefore initial (75+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 75 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_75 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 1#5 4#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 1), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 1#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 1#5 4#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_75] using ob)
#print axioms site_75
#print axioms word_75
#print axioms step_75

theorem site_76 : EntryBinding.plan.code[76]? = some (6316, 3942842500) := rfl
theorem room_76 (initial : NativeState) : 76 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_76 : NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5 = 3942842500#32 := by decide
theorem step_76 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 76 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (76+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[76]'(room_76 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6316, 3942842500) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_76
  have pc : x.regs._PC = MemReloc.imageAddress base 6316 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    76 x inv.core (6316, 3942842500) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (76+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 76 + 4#64 = offset EntryBinding.plan (76+1) from by decide)
  have draws : DefaultState.drawsBefore initial 76 ≤ DefaultState.drawsBefore initial (76+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 76 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_76 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_76] using ob)
#print axioms site_76
#print axioms word_76
#print axioms step_76

theorem site_77 : EntryBinding.plan.code[77]? = some (6320, 3666093188) := rfl
theorem room_77 (initial : NativeState) : 77 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_77 : N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5 = 3666093188#32 := by decide
theorem step_77 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 77 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (77+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[77]'(room_77 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6320, 3666093188) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_77
  have pc : x.regs._PC = MemReloc.imageAddress base 6320 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    77 x inv.core (6320, 3666093188) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (77+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 77 + 4#64 = offset EntryBinding.plan (77+1) from by decide)
  have draws : DefaultState.drawsBefore initial 77 ≤ DefaultState.drawsBefore initial (77+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 77 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_77 initial) compiles page (by decide)
    (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x inv
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_12 real x 4#5 4#5 4#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csneg_outputs x fin 4#5 4#5 4#5 vh, memory⟩)
    next (by simpa only [word_77] using ob)
#print axioms site_77
#print axioms word_77
#print axioms step_77

theorem site_78 : EntryBinding.plan.code[78]? = some (6324, 3667862505) := rfl
theorem room_78 (initial : NativeState) : 78 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_78 : NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 9#5 = 3667862505#32 := by decide
theorem step_78 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 78 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (78+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[78]'(room_78 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6324, 3667862505) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_78
  have pc : x.regs._PC = MemReloc.imageAddress base 6324 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    78 x inv.core (6324, 3667862505) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (78+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 78 + 4#64 = offset EntryBinding.plan (78+1) from by decide)
  have draws : DefaultState.drawsBefore initial 78 ≤ DefaultState.drawsBefore initial (78+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 78 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_78 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 9#5 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_2 real x 9#5 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_78] using ob)
#print axioms site_78
#print axioms word_78
#print axioms step_78

theorem site_79 : EntryBinding.plan.code[79]? = some (6328, 2870018543) := rfl
theorem room_79 (initial : NativeState) : 79 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_79 : NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 17#5 = 2870018543#32 := by decide
theorem step_79 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 79 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (79+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[79]'(room_79 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6328, 2870018543) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_79
  have pc : x.regs._PC = MemReloc.imageAddress base 6328 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    79 x inv.core (6328, 2870018543) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (79+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 79 + 4#64 = offset EntryBinding.plan (79+1) from by decide)
  have draws : DefaultState.drawsBefore initial 79 ≤ DefaultState.drawsBefore initial (79+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 79 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_79 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 15#5 15#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_79] using ob)
#print axioms site_79
#print axioms word_79
#print axioms step_79

theorem site_80 : EntryBinding.plan.code[80]? = some (6332, 2585722913) := rfl
theorem room_80 (initial : NativeState) : 80 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_80 : NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5 = 2585722913#32 := by decide
theorem step_80 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 80 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (80+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[80]'(room_80 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6332, 2585722913) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_80
  have pc : x.regs._PC = MemReloc.imageAddress base 6332 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    80 x inv.core (6332, 2585722913) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (80+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 80 + 4#64 = offset EntryBinding.plan (80+1) from by decide)
  have draws : DefaultState.drawsBefore initial 80 ≤ DefaultState.drawsBefore initial (80+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 80 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_80 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 1#5 1#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 1#5 1#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_80] using ob)
#print axioms site_80
#print axioms word_80
#print axioms step_80

theorem site_81 : EntryBinding.plan.code[81]? = some (6336, 3943039142) := rfl
theorem room_81 (initial : NativeState) : 81 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_81 : NativeEntryBodyDispatch.SubsShift64.selected 6#5 5#5 0#6 6#5 = 3943039142#32 := by decide
theorem step_81 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 81 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (81+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[81]'(room_81 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6336, 3943039142) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_81
  have pc : x.regs._PC = MemReloc.imageAddress base 6336 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    81 x inv.core (6336, 3943039142) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (81+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 81 + 4#64 = offset EntryBinding.plan (81+1) from by decide)
  have draws : DefaultState.drawsBefore initial 81 ≤ DefaultState.drawsBefore initial (81+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 81 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_81 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 6#5 5#5 0#6 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 6#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 6#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_81] using ob)
#print axioms site_81
#print axioms word_81
#print axioms step_81

theorem site_82 : EntryBinding.plan.code[82]? = some (6340, 3666224326) := rfl
theorem room_82 (initial : NativeState) : 82 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_82 : N1D226.CsnegCs64Generic.Encoding.selected 6#5 6#5 6#5 = 3666224326#32 := by decide
theorem step_82 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 82 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (82+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[82]'(room_82 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6340, 3666224326) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_82
  have pc : x.regs._PC = MemReloc.imageAddress base 6340 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    82 x inv.core (6340, 3666224326) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (82+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 82 + 4#64 = offset EntryBinding.plan (82+1) from by decide)
  have draws : DefaultState.drawsBefore initial 82 ≤ DefaultState.drawsBefore initial (82+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 82 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_82 initial) compiles page (by decide)
    (N1D226.CsnegCs64Generic.Encoding.selected 6#5 6#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 6#5 6#5 6#5) (none) x inv
    (N1D226.CsnegCs64Generic.Value.tailX real x 6#5 6#5 6#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_12 real x 6#5 6#5 6#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csneg_outputs x fin 6#5 6#5 6#5 vh, memory⟩)
    next (by simpa only [word_82] using ob)
#print axioms site_82
#print axioms word_82
#print axioms step_82

theorem site_83 : EntryBinding.plan.code[83]? = some (6344, 3666420009) := rfl
theorem room_83 (initial : NativeState) : 83 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_83 : N1D226.CsinvCs64Generic.Encoding.selected 9#5 9#5 9#5 = 3666420009#32 := by decide
theorem step_83 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 83 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (83+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[83]'(room_83 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6344, 3666420009) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_83
  have pc : x.regs._PC = MemReloc.imageAddress base 6344 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    83 x inv.core (6344, 3666420009) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (83+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 83 + 4#64 = offset EntryBinding.plan (83+1) from by decide)
  have draws : DefaultState.drawsBefore initial 83 ≤ DefaultState.drawsBefore initial (83+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 83 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_83 initial) compiles page (by decide)
    (N1D226.CsinvCs64Generic.Encoding.selected 9#5 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 9#5 9#5 9#5) (none) x inv
    (N1D226.CsinvCs64Generic.Value.tailX real x 9#5 9#5 9#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_11 real x 9#5 9#5 9#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.ConditionalExprCuts.csinv_outputs x fin 9#5 9#5 9#5 vh, memory⟩)
    next (by simpa only [word_83] using ob)
#print axioms site_83
#print axioms word_83
#print axioms step_83

theorem site_84 : EntryBinding.plan.code[84]? = some (6348, 2600893573) := rfl
theorem room_84 (initial : NativeState) : 84 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_84 : NativeEntryBodyDispatch.Madd64.selected 5#5 4#5 6#5 = 2600893573#32 := by decide
theorem step_84 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 84 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (84+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[84]'(room_84 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6348, 2600893573) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_84
  have pc : x.regs._PC = MemReloc.imageAddress base 6348 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    84 x inv.core (6348, 2600893573) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (84+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 84 + 4#64 = offset EntryBinding.plan (84+1) from by decide)
  have draws : DefaultState.drawsBefore initial 84 ≤ DefaultState.drawsBefore initial (84+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 84 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_84 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 5#5 4#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 5#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 5#5 4#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_84] using ob)
#print axioms site_84
#print axioms word_84
#print axioms step_84

theorem site_85 : EntryBinding.plan.code[85]? = some (6352, 2613476486) := rfl
theorem room_85 (initial : NativeState) : 85 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_85 : NativeEntryBodyDispatch.Umulh64.selected 6#5 4#5 6#5 = 2613476486#32 := by decide
theorem step_85 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 85 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (85+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[85]'(room_85 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6352, 2613476486) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_85
  have pc : x.regs._PC = MemReloc.imageAddress base 6352 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    85 x inv.core (6352, 2613476486) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (85+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 85 + 4#64 = offset EntryBinding.plan (85+1) from by decide)
  have draws : DefaultState.drawsBefore initial 85 ≤ DefaultState.drawsBefore initial (85+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 85 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_85 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 6#5 4#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 6#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 6#5 4#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_85] using ob)
#print axioms site_85
#print axioms word_85
#print axioms step_85

theorem site_86 : EntryBinding.plan.code[86]? = some (6356, 2869887057) := rfl
theorem room_86 (initial : NativeState) : 86 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_86 : NativeEntryBodyDispatch.AddsShift64.selected 17#5 2#5 0#6 15#5 = 2869887057#32 := by decide
theorem step_86 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 86 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (86+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[86]'(room_86 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6356, 2869887057) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_86
  have pc : x.regs._PC = MemReloc.imageAddress base 6356 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    86 x inv.core (6356, 2869887057) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (86+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 86 + 4#64 = offset EntryBinding.plan (86+1) from by decide)
  have draws : DefaultState.drawsBefore initial 86 ≤ DefaultState.drawsBefore initial (86+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 86 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_86 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 17#5 2#5 0#6 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 17), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 17#5 2#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 17#5 2#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_86] using ob)
#print axioms site_86
#print axioms word_86
#print axioms step_86

theorem site_87 : EntryBinding.plan.code[87]? = some (6360, 3120628207) := rfl
theorem room_87 (initial : NativeState) : 87 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_87 : NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 1#5 = 3120628207#32 := by decide
theorem step_87 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 87 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (87+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[87]'(room_87 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6360, 3120628207) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_87
  have pc : x.regs._PC = MemReloc.imageAddress base 6360 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    87 x inv.core (6360, 3120628207) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (87+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 87 + 4#64 = offset EntryBinding.plan (87+1) from by decide)
  have draws : DefaultState.drawsBefore initial 87 ≤ DefaultState.drawsBefore initial (87+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 87 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_87 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 1#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 1#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 15#5 15#5 1#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_87] using ob)
#print axioms site_87
#print axioms word_87
#print axioms step_87

theorem site_88 : EntryBinding.plan.code[88]? = some (6364, 2585722913) := rfl
theorem room_88 (initial : NativeState) : 88 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_88 : NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5 = 2585722913#32 := by decide
theorem step_88 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 88 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (88+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[88]'(room_88 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6364, 2585722913) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_88
  have pc : x.regs._PC = MemReloc.imageAddress base 6364 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    88 x inv.core (6364, 2585722913) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (88+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 88 + 4#64 = offset EntryBinding.plan (88+1) from by decide)
  have draws : DefaultState.drawsBefore initial 88 ≤ DefaultState.drawsBefore initial (88+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 88 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_88 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 1#5 1#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 1#5 1#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_88] using ob)
#print axioms site_88
#print axioms word_88
#print axioms step_88

theorem site_89 : EntryBinding.plan.code[89]? = some (6368, 2969568575) := rfl
theorem room_89 (initial : NativeState) : 89 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_89 : N1D226.CmnImm64Generic.Encoding.selected 9#5 1#12 = 2969568575#32 := by decide
theorem step_89 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 89 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (89+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[89]'(room_89 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6368, 2969568575) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_89
  have pc : x.regs._PC = MemReloc.imageAddress base 6368 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    89 x inv.core (6368, 2969568575) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (89+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 89 + 4#64 = offset EntryBinding.plan (89+1) from by decide)
  have draws : DefaultState.drawsBefore initial 89 ≤ DefaultState.drawsBefore initial (89+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 89 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_89 initial) compiles page (by decide)
    (N1D226.CmnImm64Generic.Encoding.selected 9#5 1#12) _ _ (fun s => s.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩)) (by rfl) x inv
    (N1D226.CmnImm64Generic.Value.tailX real x 9#5 1#12 (by decide)) (TranslateScalarTagCheck.Runtime.tail_10 real x 9#5 1#12 (by decide)) next (by simpa only [word_89] using ob)
#print axioms site_89
#print axioms word_89
#print axioms step_89

theorem site_90 : EntryBinding.plan.code[90]? = some (6372, 3389587621) := rfl
theorem room_90 (initial : NativeState) : 90 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_90 : NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 9#5 = 3389587621#32 := by decide
theorem step_90 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 90 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (90+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[90]'(room_90 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6372, 3389587621) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_90
  have pc : x.regs._PC = MemReloc.imageAddress base 6372 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    90 x inv.core (6372, 3389587621) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (90+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 90 + 4#64 = offset EntryBinding.plan (90+1) from by decide)
  have draws : DefaultState.drawsBefore initial 90 ≤ DefaultState.drawsBefore initial (90+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 90 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_90 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.eor, [.reg (.x 5), .reg (.x 9)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_90] using ob)
#print axioms site_90
#print axioms word_90
#print axioms step_90

theorem site_91 : EntryBinding.plan.code[91]? = some (6376, 3121676465) := rfl
theorem room_91 (initial : NativeState) : 91 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_91 : NativeEntryBodyDispatch.Adcs64.selected 17#5 5#5 17#5 = 3121676465#32 := by decide
theorem step_91 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 91 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (91+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[91]'(room_91 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6376, 3121676465) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_91
  have pc : x.regs._PC = MemReloc.imageAddress base 6376 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    91 x inv.core (6376, 3121676465) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (91+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 91 + 4#64 = offset EntryBinding.plan (91+1) from by decide)
  have draws : DefaultState.drawsBefore initial 91 ≤ DefaultState.drawsBefore initial (91+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 91 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_91 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 17#5 5#5 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 17), some ⟨.add3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 17#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 17#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_91] using ob)
#print axioms site_91
#print axioms word_91
#print axioms step_91

theorem site_92 : EntryBinding.plan.code[92]? = some (6380, 3389587654) := rfl
theorem room_92 (initial : NativeState) : 92 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_92 : NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 9#5 = 3389587654#32 := by decide
theorem step_92 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 92 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (92+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[92]'(room_92 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6380, 3389587654) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_92
  have pc : x.regs._PC = MemReloc.imageAddress base 6380 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    92 x inv.core (6380, 3389587654) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (92+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 92 + 4#64 = offset EntryBinding.plan (92+1) from by decide)
  have draws : DefaultState.drawsBefore initial 92 ≤ DefaultState.drawsBefore initial (92+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 92 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_92 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.eor, [.reg (.x 6), .reg (.x 9)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_92] using ob)
#print axioms site_92
#print axioms word_92
#print axioms step_92

theorem site_93 : EntryBinding.plan.code[93]? = some (6384, 3121545423) := rfl
theorem room_93 (initial : NativeState) : 93 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_93 : NativeEntryBodyDispatch.Adcs64.selected 15#5 6#5 15#5 = 3121545423#32 := by decide
theorem step_93 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 93 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (93+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[93]'(room_93 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6384, 3121545423) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_93
  have pc : x.regs._PC = MemReloc.imageAddress base 6384 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    93 x inv.core (6384, 3121545423) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (93+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 93 + 4#64 = offset EntryBinding.plan (93+1) from by decide)
  have draws : DefaultState.drawsBefore initial 93 ≤ DefaultState.drawsBefore initial (93+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 93 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_93 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 15#5 6#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 15#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 15#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_93] using ob)
#print axioms site_93
#print axioms word_93
#print axioms step_93

theorem site_94 : EntryBinding.plan.code[94]? = some (6388, 2584281121) := rfl
theorem room_94 (initial : NativeState) : 94 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_94 : NativeEntryBodyDispatch.Adc64.selected 1#5 1#5 9#5 = 2584281121#32 := by decide
theorem step_94 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 94 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (94+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[94]'(room_94 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6388, 2584281121) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_94
  have pc : x.regs._PC = MemReloc.imageAddress base 6388 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    94 x inv.core (6388, 2584281121) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (94+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 94 + 4#64 = offset EntryBinding.plan (94+1) from by decide)
  have draws : DefaultState.drawsBefore initial 94 ≤ DefaultState.drawsBefore initial (94+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 94 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_94 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 1#5 1#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .reg (.x 9), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 1#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 1#5 1#5 9#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_94] using ob)
#print axioms site_94
#print axioms word_94
#print axioms step_94

theorem site_95 : EntryBinding.plan.code[95]? = some (6392, 2869363049) := rfl
theorem room_95 (initial : NativeState) : 95 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_95 : NativeEntryBodyDispatch.AddsShift64.selected 9#5 11#5 0#6 7#5 = 2869363049#32 := by decide
theorem step_95 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 95 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (95+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[95]'(room_95 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6392, 2869363049) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_95
  have pc : x.regs._PC = MemReloc.imageAddress base 6392 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    95 x inv.core (6392, 2869363049) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (95+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 95 + 4#64 = offset EntryBinding.plan (95+1) from by decide)
  have draws : DefaultState.drawsBefore initial 95 ≤ DefaultState.drawsBefore initial (95+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 95 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_95 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 9#5 11#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 9#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 9#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_95] using ob)
#print axioms site_95
#print axioms word_95
#print axioms step_95

theorem site_96 : EntryBinding.plan.code[96]? = some (6396, 3121086858) := rfl
theorem room_96 (initial : NativeState) : 96 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_96 : NativeEntryBodyDispatch.Adcs64.selected 10#5 12#5 8#5 = 3121086858#32 := by decide
theorem step_96 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 96 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (96+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[96]'(room_96 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6396, 3121086858) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_96
  have pc : x.regs._PC = MemReloc.imageAddress base 6396 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    96 x inv.core (6396, 3121086858) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (96+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 96 + 4#64 = offset EntryBinding.plan (96+1) from by decide)
  have draws : DefaultState.drawsBefore initial 96 ≤ DefaultState.drawsBefore initial (96+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 96 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_96 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 10#5 12#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 10#5 12#5 8#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 10#5 12#5 8#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_96] using ob)
#print axioms site_96
#print axioms word_96
#print axioms step_96

theorem site_97 : EntryBinding.plan.code[97]? = some (6400, 3121283499) := rfl
theorem room_97 (initial : NativeState) : 97 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_97 : NativeEntryBodyDispatch.Adcs64.selected 11#5 13#5 11#5 = 3121283499#32 := by decide
theorem step_97 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 97 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (97+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[97]'(room_97 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6400, 3121283499) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_97
  have pc : x.regs._PC = MemReloc.imageAddress base 6400 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    97 x inv.core (6400, 3121283499) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (97+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 97 + 4#64 = offset EntryBinding.plan (97+1) from by decide)
  have draws : DefaultState.drawsBefore initial 97 ≤ DefaultState.drawsBefore initial (97+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 97 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_97 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 11#5 13#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 11#5 13#5 11#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 11#5 13#5 11#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_97] using ob)
#print axioms site_97
#print axioms word_97
#print axioms step_97

theorem site_98 : EntryBinding.plan.code[98]? = some (6404, 3121349068) := rfl
theorem room_98 (initial : NativeState) : 98 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_98 : NativeEntryBodyDispatch.Adcs64.selected 12#5 14#5 12#5 = 3121349068#32 := by decide
theorem step_98 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 98 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (98+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[98]'(room_98 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6404, 3121349068) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_98
  have pc : x.regs._PC = MemReloc.imageAddress base 6404 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    98 x inv.core (6404, 3121349068) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (98+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 98 + 4#64 = offset EntryBinding.plan (98+1) from by decide)
  have draws : DefaultState.drawsBefore initial 98 ≤ DefaultState.drawsBefore initial (98+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 98 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_98 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 12#5 14#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 12#5 14#5 12#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 12#5 14#5 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_98] using ob)
#print axioms site_98
#print axioms word_98
#print axioms step_98

theorem site_99 : EntryBinding.plan.code[99]? = some (6408, 3122594221) := rfl
theorem room_99 (initial : NativeState) : 99 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_99 : NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5 = 3122594221#32 := by decide
theorem step_99 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 99 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (99+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[99]'(room_99 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6408, 3122594221) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_99
  have pc : x.regs._PC = MemReloc.imageAddress base 6408 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    99 x inv.core (6408, 3122594221) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (99+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 99 + 4#64 = offset EntryBinding.plan (99+1) from by decide)
  have draws : DefaultState.drawsBefore initial 99 ≤ DefaultState.drawsBefore initial (99+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 99 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_99 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 13#5 13#5 (by decide) (by decide) (by decide)) next (by simpa only [word_99] using ob)
#print axioms site_99
#print axioms word_99
#print axioms step_99

theorem site_100 : EntryBinding.plan.code[100]? = some (6412, 2585723342) := rfl
theorem room_100 (initial : NativeState) : 100 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_100 : NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5 = 2585723342#32 := by decide
theorem step_100 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 100 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (100+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[100]'(room_100 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6412, 2585723342) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_100
  have pc : x.regs._PC = MemReloc.imageAddress base 6412 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    100 x inv.core (6412, 2585723342) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (100+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 100 + 4#64 = offset EntryBinding.plan (100+1) from by decide)
  have draws : DefaultState.drawsBefore initial 100 ≤ DefaultState.drawsBefore initial (100+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 100 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_100 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_100] using ob)
#print axioms site_100
#print axioms word_100
#print axioms step_100

theorem site_101 : EntryBinding.plan.code[101]? = some (6416, 2969568799) := rfl
theorem room_101 (initial : NativeState) : 101 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_101 : N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12 = 2969568799#32 := by decide
theorem step_101 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 101 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (101+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[101]'(room_101 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6416, 2969568799) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_101
  have pc : x.regs._PC = MemReloc.imageAddress base 6416 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    101 x inv.core (6416, 2969568799) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (101+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 101 + 4#64 = offset EntryBinding.plan (101+1) from by decide)
  have draws : DefaultState.drawsBefore initial 101 ≤ DefaultState.drawsBefore initial (101+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 101 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_101 initial) compiles page (by decide)
    (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ _ (fun s => s.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) (by rfl) x inv
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) (TranslateScalarTagCheck.Runtime.tail_10 real x 16#5 1#12 (by decide)) next (by simpa only [word_101] using ob)
#print axioms site_101
#print axioms word_101
#print axioms step_101

theorem site_102 : EntryBinding.plan.code[102]? = some (6420, 3390046274) := rfl
theorem room_102 (initial : NativeState) : 102 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_102 : NativeEntryBodyDispatch.SecpEor64.selected 2#5 2#5 16#5 = 3390046274#32 := by decide
theorem step_102 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 102 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (102+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[102]'(room_102 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6420, 3390046274) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_102
  have pc : x.regs._PC = MemReloc.imageAddress base 6420 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    102 x inv.core (6420, 3390046274) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (102+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 102 + 4#64 = offset EntryBinding.plan (102+1) from by decide)
  have draws : DefaultState.drawsBefore initial 102 ≤ DefaultState.drawsBefore initial (102+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 102 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_102 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 2#5 2#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨.eor, [.reg (.x 2), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 2#5 2#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 2#5 2#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_102] using ob)
#print axioms site_102
#print axioms word_102
#print axioms step_102

theorem site_103 : EntryBinding.plan.code[103]? = some (6424, 3121152073) := rfl
theorem room_103 (initial : NativeState) : 103 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_103 : NativeEntryBodyDispatch.Adcs64.selected 9#5 2#5 9#5 = 3121152073#32 := by decide
theorem step_103 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 103 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (103+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[103]'(room_103 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6424, 3121152073) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_103
  have pc : x.regs._PC = MemReloc.imageAddress base 6424 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    103 x inv.core (6424, 3121152073) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (103+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 103 + 4#64 = offset EntryBinding.plan (103+1) from by decide)
  have draws : DefaultState.drawsBefore initial 103 ≤ DefaultState.drawsBefore initial (103+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 103 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_103 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 9#5 2#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 9#5 2#5 9#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 9#5 2#5 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_103] using ob)
#print axioms site_103
#print axioms word_103
#print axioms step_103

theorem site_104 : EntryBinding.plan.code[104]? = some (6428, 3390046769) := rfl
theorem room_104 (initial : NativeState) : 104 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_104 : NativeEntryBodyDispatch.SecpEor64.selected 17#5 17#5 16#5 = 3390046769#32 := by decide
theorem step_104 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 104 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (104+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[104]'(room_104 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6428, 3390046769) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_104
  have pc : x.regs._PC = MemReloc.imageAddress base 6428 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    104 x inv.core (6428, 3390046769) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (104+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 104 + 4#64 = offset EntryBinding.plan (104+1) from by decide)
  have draws : DefaultState.drawsBefore initial 104 ≤ DefaultState.drawsBefore initial (104+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 104 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_104 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 17#5 17#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 17), some ⟨.eor, [.reg (.x 17), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 17#5 17#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 17#5 17#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_104] using ob)
#print axioms site_104
#print axioms word_104
#print axioms step_104

theorem site_105 : EntryBinding.plan.code[105]? = some (6432, 3121218090) := rfl
theorem room_105 (initial : NativeState) : 105 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_105 : NativeEntryBodyDispatch.Adcs64.selected 10#5 17#5 10#5 = 3121218090#32 := by decide
theorem step_105 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 105 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (105+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[105]'(room_105 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6432, 3121218090) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_105
  have pc : x.regs._PC = MemReloc.imageAddress base 6432 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    105 x inv.core (6432, 3121218090) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (105+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 105 + 4#64 = offset EntryBinding.plan (105+1) from by decide)
  have draws : DefaultState.drawsBefore initial 105 ≤ DefaultState.drawsBefore initial (105+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 105 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_105 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 10#5 17#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 10#5 17#5 10#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 10#5 17#5 10#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_105] using ob)
#print axioms site_105
#print axioms word_105
#print axioms step_105

theorem site_106 : EntryBinding.plan.code[106]? = some (6436, 3390046703) := rfl
theorem room_106 (initial : NativeState) : 106 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_106 : NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5 = 3390046703#32 := by decide
theorem step_106 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 106 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (106+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[106]'(room_106 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6436, 3390046703) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_106
  have pc : x.regs._PC = MemReloc.imageAddress base 6436 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    106 x inv.core (6436, 3390046703) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (106+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 106 + 4#64 = offset EntryBinding.plan (106+1) from by decide)
  have draws : DefaultState.drawsBefore initial 106 ≤ DefaultState.drawsBefore initial (106+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 106 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_106 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_106] using ob)
#print axioms site_106
#print axioms word_106
#print axioms step_106

theorem site_107 : EntryBinding.plan.code[107]? = some (6440, 3121283563) := rfl
theorem room_107 (initial : NativeState) : 107 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_107 : NativeEntryBodyDispatch.Adcs64.selected 11#5 15#5 11#5 = 3121283563#32 := by decide
theorem step_107 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 107 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (107+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[107]'(room_107 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6440, 3121283563) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_107
  have pc : x.regs._PC = MemReloc.imageAddress base 6440 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    107 x inv.core (6440, 3121283563) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (107+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 107 + 4#64 = offset EntryBinding.plan (107+1) from by decide)
  have draws : DefaultState.drawsBefore initial 107 ≤ DefaultState.drawsBefore initial (107+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 107 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_107 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 11#5 15#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 11#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 11#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_107] using ob)
#print axioms site_107
#print axioms word_107
#print axioms step_107

theorem site_108 : EntryBinding.plan.code[108]? = some (6444, 3390046241) := rfl
theorem room_108 (initial : NativeState) : 108 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_108 : NativeEntryBodyDispatch.SecpEor64.selected 1#5 1#5 16#5 = 3390046241#32 := by decide
theorem step_108 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 108 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (108+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[108]'(room_108 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6444, 3390046241) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_108
  have pc : x.regs._PC = MemReloc.imageAddress base 6444 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    108 x inv.core (6444, 3390046241) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (108+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 108 + 4#64 = offset EntryBinding.plan (108+1) from by decide)
  have draws : DefaultState.drawsBefore initial 108 ≤ DefaultState.drawsBefore initial (108+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 108 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_108 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 1#5 1#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 1), some ⟨.eor, [.reg (.x 1), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 1#5 1#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 1#5 1#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_108] using ob)
#print axioms site_108
#print axioms word_108
#print axioms step_108

theorem site_109 : EntryBinding.plan.code[109]? = some (6448, 3121348652) := rfl
theorem room_109 (initial : NativeState) : 109 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_109 : NativeEntryBodyDispatch.Adcs64.selected 12#5 1#5 12#5 = 3121348652#32 := by decide
theorem step_109 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 109 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (109+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[109]'(room_109 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6448, 3121348652) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_109
  have pc : x.regs._PC = MemReloc.imageAddress base 6448 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    109 x inv.core (6448, 3121348652) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (109+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 109 + 4#64 = offset EntryBinding.plan (109+1) from by decide)
  have draws : DefaultState.drawsBefore initial 109 ≤ DefaultState.drawsBefore initial (109+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 109 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_109 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 12#5 1#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 12#5 1#5 12#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 12#5 1#5 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_109] using ob)
#print axioms site_109
#print axioms word_109
#print axioms step_109

theorem site_110 : EntryBinding.plan.code[110]? = some (6452, 3121611181) := rfl
theorem room_110 (initial : NativeState) : 110 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_110 : NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 16#5 = 3121611181#32 := by decide
theorem step_110 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 110 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (110+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[110]'(room_110 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6452, 3121611181) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_110
  have pc : x.regs._PC = MemReloc.imageAddress base 6452 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    110 x inv.core (6452, 3121611181) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (110+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 110 + 4#64 = offset EntryBinding.plan (110+1) from by decide)
  have draws : DefaultState.drawsBefore initial 110 ≤ DefaultState.drawsBefore initial (110+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 110 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_110 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 13#5 13#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_110] using ob)
#print axioms site_110
#print axioms word_110
#print axioms step_110

theorem site_111 : EntryBinding.plan.code[111]? = some (6456, 2584740302) := rfl
theorem room_111 (initial : NativeState) : 111 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_111 : NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5 = 2584740302#32 := by decide
theorem step_111 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 111 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (111+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[111]'(room_111 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6456, 2584740302) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_111
  have pc : x.regs._PC = MemReloc.imageAddress base 6456 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    111 x inv.core (6456, 2584740302) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (111+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 111 + 4#64 = offset EntryBinding.plan (111+1) from by decide)
  have draws : DefaultState.drawsBefore initial 111 ≤ DefaultState.drawsBefore initial (111+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 111 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_111 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 16), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_111] using ob)
#print axioms site_111
#print axioms word_111
#print axioms step_111

theorem site_112 : EntryBinding.plan.code[112]? = some (6460, 3531635248) := rfl
theorem room_112 (initial : NativeState) : 112 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_112 : NativeEntryBodyDispatch.Movz64z.selected 16#5 977#16 = 3531635248#32 := by decide
theorem step_112 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 112 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (112+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[112]'(room_112 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6460, 3531635248) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_112
  have pc : x.regs._PC = MemReloc.imageAddress base 6460 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    112 x inv.core (6460, 3531635248) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (112+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 112 + 4#64 = offset EntryBinding.plan (112+1) from by decide)
  have draws : DefaultState.drawsBefore initial 112 ≤ DefaultState.drawsBefore initial (112+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 112 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_112 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Movz64z.selected 16#5 977#16) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨(.const 977#64), []⟩)] (none) (by rfl) x inv
    (ArmCertValue.Movz64z.tailX real x 16#5 977#16 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_2 real x 16#5 977#16 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_112] using ob)
#print axioms site_112
#print axioms word_112
#print axioms step_112

theorem site_113 : EntryBinding.plan.code[113]? = some (6464, 2992636417) := rfl
theorem room_113 (initial : NativeState) : 113 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_113 : NativeEntryBodyDispatch.OrrImm32_0.selected 1#5 16#5 = 2992636417#32 := by decide
theorem step_113 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 113 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (113+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[113]'(room_113 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6464, 2992636417) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_113
  have pc : x.regs._PC = MemReloc.imageAddress base 6464 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    113 x inv.core (6464, 2992636417) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (113+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 113 + 4#64 = offset EntryBinding.plan (113+1) from by decide)
  have draws : DefaultState.drawsBefore initial 113 ≤ DefaultState.drawsBefore initial (113+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 113 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_113 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.OrrImm32_0.selected 1#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 1), some ⟨.orr, [.reg (.x 16), .lit 4294967296#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.OrrImm32_0.tailX real x 1#5 16#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_8 real x 1#5 16#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_113] using ob)
#print axioms site_113
#print axioms word_113
#print axioms step_113

theorem site_114 : EntryBinding.plan.code[114]? = some (6468, 2601221155) := rfl
theorem room_114 (initial : NativeState) : 114 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_114 : NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 11#5 = 2601221155#32 := by decide
theorem step_114 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 114 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (114+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[114]'(room_114 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6468, 2601221155) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_114
  have pc : x.regs._PC = MemReloc.imageAddress base 6468 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    114 x inv.core (6468, 2601221155) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (114+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 114 + 4#64 = offset EntryBinding.plan (114+1) from by decide)
  have draws : DefaultState.drawsBefore initial 114 ≤ DefaultState.drawsBefore initial (114+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 114 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_114 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 1), .reg (.x 11)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 3#5 1#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 3#5 1#5 11#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_114] using ob)
#print axioms site_114
#print axioms word_114
#print axioms step_114

theorem site_115 : EntryBinding.plan.code[115]? = some (6472, 2613804069) := rfl
theorem room_115 (initial : NativeState) : 115 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_115 : NativeEntryBodyDispatch.Umulh64.selected 5#5 1#5 11#5 = 2613804069#32 := by decide
theorem step_115 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 115 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (115+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[115]'(room_115 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6472, 2613804069) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_115
  have pc : x.regs._PC = MemReloc.imageAddress base 6472 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    115 x inv.core (6472, 2613804069) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (115+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 115 + 4#64 = offset EntryBinding.plan (115+1) from by decide)
  have draws : DefaultState.drawsBefore initial 115 ≤ DefaultState.drawsBefore initial (115+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 115 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_115 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 5#5 1#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 1), .reg (.x 11)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 5#5 1#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 5#5 1#5 11#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_115] using ob)
#print axioms site_115
#print axioms word_115
#print axioms step_115

theorem site_116 : EntryBinding.plan.code[116]? = some (6476, 2453699983) := rfl
theorem room_116 (initial : NativeState) : 116 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_116 : NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 12#5 = 2453699983#32 := by decide
theorem step_116 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 116 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (116+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[116]'(room_116 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6476, 2453699983) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_116
  have pc : x.regs._PC = MemReloc.imageAddress base 6476 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    116 x inv.core (6476, 2453699983) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (116+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 116 + 4#64 = offset EntryBinding.plan (116+1) from by decide)
  have draws : DefaultState.drawsBefore initial 116 ≤ DefaultState.drawsBefore initial (116+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 116 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_116 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.and, [.reg (.x 12), .lit 4294967295#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpAndMask32.tailX real x 15#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_0 real x 15#5 12#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_116] using ob)
#print axioms site_116
#print axioms word_116
#print axioms step_116

theorem site_117 : EntryBinding.plan.code[117]? = some (6480, 3546348930) := rfl
theorem room_117 (initial : NativeState) : 117 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_117 : NativeEntryBodyDispatch.SecpLsr32.selected 2#5 12#5 = 3546348930#32 := by decide
theorem step_117 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 117 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (117+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[117]'(room_117 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6480, 3546348930) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_117
  have pc : x.regs._PC = MemReloc.imageAddress base 6480 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    117 x inv.core (6480, 3546348930) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (117+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 117 + 4#64 = offset EntryBinding.plan (117+1) from by decide)
  have draws : DefaultState.drawsBefore initial 117 ≤ DefaultState.drawsBefore initial (117+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 117 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_117 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr32.selected 2#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨(.lsr 32), [.reg (.x 12)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 2#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 2#5 12#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_117] using ob)
#print axioms site_117
#print axioms word_117
#print axioms step_117

theorem site_118 : EntryBinding.plan.code[118]? = some (6484, 2601483780) := rfl
theorem room_118 (initial : NativeState) : 118 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_118 : NativeEntryBodyDispatch.Madd64.selected 4#5 16#5 15#5 = 2601483780#32 := by decide
theorem step_118 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 118 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (118+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[118]'(room_118 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6484, 2601483780) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_118
  have pc : x.regs._PC = MemReloc.imageAddress base 6484 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    118 x inv.core (6484, 2601483780) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (118+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 118 + 4#64 = offset EntryBinding.plan (118+1) from by decide)
  have draws : DefaultState.drawsBefore initial 118 ≤ DefaultState.drawsBefore initial (118+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 118 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_118 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 4#5 16#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 16), .reg (.x 15)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 4#5 16#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 4#5 16#5 15#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_118] using ob)
#print axioms site_118
#print axioms word_118
#print axioms step_118

theorem site_119 : EntryBinding.plan.code[119]? = some (6488, 2600615439) := rfl
theorem room_119 (initial : NativeState) : 119 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_119 : N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5 = 2600615439#32 := by decide
theorem step_119 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 119 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (119+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[119]'(room_119 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6488, 2600615439) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_119
  have pc : x.regs._PC = MemReloc.imageAddress base 6488 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    119 x inv.core (6488, 2600615439) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (119+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 119 + 4#64 = offset EntryBinding.plan (119+1) from by decide)
  have draws : DefaultState.drawsBefore initial 119 ≤ DefaultState.drawsBefore initial (119+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 119 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_119 initial) compiles page (by decide)
    (N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 15#5 16#5 15#5 2#5) (none) x inv
    (N1D226.Madd64Generic.DriverValue.tailX real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_5 real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.madd_outputs x fin 15#5 16#5 15#5 2#5 vh, memory⟩)
    next (by simpa only [word_119] using ob)
#print axioms site_119
#print axioms word_119
#print axioms step_119

theorem site_120 : EntryBinding.plan.code[120]? = some (6492, 2869919876) := rfl
theorem room_120 (initial : NativeState) : 120 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_120 : N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 32#6 15#5 = 2869919876#32 := by decide
theorem step_120 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 120 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (120+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[120]'(room_120 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6492, 2869919876) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_120
  have pc : x.regs._PC = MemReloc.imageAddress base 6492 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    120 x inv.core (6492, 2869919876) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (120+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 120 + 4#64 = offset EntryBinding.plan (120+1) from by decide)
  have draws : DefaultState.drawsBefore initial 120 ≤ DefaultState.drawsBefore initial (120+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 120 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_120 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 32#6 15#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 4#5 4#5 32#6 15#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 4#5 32#6 15#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 4#5 4#5 32#6 15#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 4#5 4#5 32#6 15#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 4#5 4#5 32#6 15#5 vh, memory⟩)
    next (by simpa only [word_120] using ob)
#print axioms site_120
#print axioms word_120
#print axioms step_120

theorem site_121 : EntryBinding.plan.code[121]? = some (6496, 3546349039) := rfl
theorem room_121 (initial : NativeState) : 121 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_121 : NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5 = 3546349039#32 := by decide
theorem step_121 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 121 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (121+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[121]'(room_121 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6496, 3546349039) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_121
  have pc : x.regs._PC = MemReloc.imageAddress base 6496 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    121 x inv.core (6496, 3546349039) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (121+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 121 + 4#64 = offset EntryBinding.plan (121+1) from by decide)
  have draws : DefaultState.drawsBefore initial 121 ≤ DefaultState.drawsBefore initial (121+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 121 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_121 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨(.lsr 32), [.reg (.x 15)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 15#5 15#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_121] using ob)
#print axioms site_121
#print axioms word_121
#print axioms step_121

theorem site_122 : EntryBinding.plan.code[122]? = some (6500, 2584674374) := rfl
theorem room_122 (initial : NativeState) : 122 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_122 : NativeEntryBodyDispatch.Adc64.selected 6#5 2#5 15#5 = 2584674374#32 := by decide
theorem step_122 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 122 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (122+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[122]'(room_122 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6500, 2584674374) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_122
  have pc : x.regs._PC = MemReloc.imageAddress base 6500 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    122 x inv.core (6500, 2584674374) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (122+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 122 + 4#64 = offset EntryBinding.plan (122+1) from by decide)
  have draws : DefaultState.drawsBefore initial 122 ≤ DefaultState.drawsBefore initial (122+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 122 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_122 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 6#5 2#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 6#5 2#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 6#5 2#5 15#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_122] using ob)
#print axioms site_122
#print axioms word_122
#print axioms step_122

theorem site_123 : EntryBinding.plan.code[123]? = some (6504, 2601352235) := rfl
theorem room_123 (initial : NativeState) : 123 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_123 : NativeEntryBodyDispatch.Madd64.selected 11#5 1#5 13#5 = 2601352235#32 := by decide
theorem step_123 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 123 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (123+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[123]'(room_123 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6504, 2601352235) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_123
  have pc : x.regs._PC = MemReloc.imageAddress base 6504 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    123 x inv.core (6504, 2601352235) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (123+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 123 + 4#64 = offset EntryBinding.plan (123+1) from by decide)
  have draws : DefaultState.drawsBefore initial 123 ≤ DefaultState.drawsBefore initial (123+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 123 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_123 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 11#5 1#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 1), .reg (.x 13)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 11#5 1#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 11#5 1#5 13#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_123] using ob)
#print axioms site_123
#print axioms word_123
#print axioms step_123

theorem site_124 : EntryBinding.plan.code[124]? = some (6508, 2613935149) := rfl
theorem room_124 (initial : NativeState) : 124 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_124 : NativeEntryBodyDispatch.Umulh64.selected 13#5 1#5 13#5 = 2613935149#32 := by decide
theorem step_124 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 124 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (124+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[124]'(room_124 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6508, 2613935149) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_124
  have pc : x.regs._PC = MemReloc.imageAddress base 6508 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    124 x inv.core (6508, 2613935149) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (124+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 124 + 4#64 = offset EntryBinding.plan (124+1) from by decide)
  have draws : DefaultState.drawsBefore initial 124 ≤ DefaultState.drawsBefore initial (124+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 124 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_124 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 13#5 1#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 1), .reg (.x 13)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 13#5 1#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 13#5 1#5 13#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_124] using ob)
#print axioms site_124
#print axioms word_124
#print axioms step_124

theorem site_125 : EntryBinding.plan.code[125]? = some (6512, 2453700047) := rfl
theorem room_125 (initial : NativeState) : 125 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_125 : NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 14#5 = 2453700047#32 := by decide
theorem step_125 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 125 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (125+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[125]'(room_125 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6512, 2453700047) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_125
  have pc : x.regs._PC = MemReloc.imageAddress base 6512 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    125 x inv.core (6512, 2453700047) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (125+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 125 + 4#64 = offset EntryBinding.plan (125+1) from by decide)
  have draws : DefaultState.drawsBefore initial 125 ≤ DefaultState.drawsBefore initial (125+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 125 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_125 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.and, [.reg (.x 14), .lit 4294967295#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpAndMask32.tailX real x 15#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_0 real x 15#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_125] using ob)
#print axioms site_125
#print axioms word_125
#print axioms step_125

theorem site_126 : EntryBinding.plan.code[126]? = some (6516, 3546348994) := rfl
theorem room_126 (initial : NativeState) : 126 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_126 : NativeEntryBodyDispatch.SecpLsr32.selected 2#5 14#5 = 3546348994#32 := by decide
theorem step_126 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 126 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (126+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[126]'(room_126 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6516, 3546348994) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_126
  have pc : x.regs._PC = MemReloc.imageAddress base 6516 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    126 x inv.core (6516, 3546348994) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (126+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 126 + 4#64 = offset EntryBinding.plan (126+1) from by decide)
  have draws : DefaultState.drawsBefore initial 126 ≤ DefaultState.drawsBefore initial (126+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 126 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_126 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr32.selected 2#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨(.lsr 32), [.reg (.x 14)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 2#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 2#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_126] using ob)
#print axioms site_126
#print axioms word_126
#print axioms step_126

theorem site_127 : EntryBinding.plan.code[127]? = some (6520, 2601483788) := rfl
theorem room_127 (initial : NativeState) : 127 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_127 : NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 15#5 = 2601483788#32 := by decide
theorem step_127 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 127 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (127+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[127]'(room_127 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6520, 2601483788) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_127
  have pc : x.regs._PC = MemReloc.imageAddress base 6520 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    127 x inv.core (6520, 2601483788) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (127+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 127 + 4#64 = offset EntryBinding.plan (127+1) from by decide)
  have draws : DefaultState.drawsBefore initial 127 ≤ DefaultState.drawsBefore initial (127+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 127 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_127 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 16), .reg (.x 15)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 12#5 16#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 12#5 16#5 15#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_127] using ob)
#print axioms site_127
#print axioms word_127
#print axioms step_127

theorem site_128 : EntryBinding.plan.code[128]? = some (6524, 2600615439) := rfl
theorem room_128 (initial : NativeState) : 128 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_128 : N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5 = 2600615439#32 := by decide
theorem step_128 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 128 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (128+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[128]'(room_128 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6524, 2600615439) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_128
  have pc : x.regs._PC = MemReloc.imageAddress base 6524 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    128 x inv.core (6524, 2600615439) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (128+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 128 + 4#64 = offset EntryBinding.plan (128+1) from by decide)
  have draws : DefaultState.drawsBefore initial 128 ≤ DefaultState.drawsBefore initial (128+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 128 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_128 initial) compiles page (by decide)
    (N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 15#5 16#5 15#5 2#5) (none) x inv
    (N1D226.Madd64Generic.DriverValue.tailX real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_5 real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.madd_outputs x fin 15#5 16#5 15#5 2#5 vh, memory⟩)
    next (by simpa only [word_128] using ob)
#print axioms site_128
#print axioms word_128
#print axioms step_128

theorem site_129 : EntryBinding.plan.code[129]? = some (6528, 2869920140) := rfl
theorem room_129 (initial : NativeState) : 129 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_129 : N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 32#6 15#5 = 2869920140#32 := by decide
theorem step_129 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 129 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (129+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[129]'(room_129 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6528, 2869920140) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_129
  have pc : x.regs._PC = MemReloc.imageAddress base 6528 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    129 x inv.core (6528, 2869920140) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (129+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 129 + 4#64 = offset EntryBinding.plan (129+1) from by decide)
  have draws : DefaultState.drawsBefore initial 129 ≤ DefaultState.drawsBefore initial (129+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 129 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_129 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 32#6 15#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 12#5 12#5 32#6 15#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 12#5 32#6 15#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 12#5 12#5 32#6 15#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 12#5 12#5 32#6 15#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 12#5 12#5 32#6 15#5 vh, memory⟩)
    next (by simpa only [word_129] using ob)
#print axioms site_129
#print axioms word_129
#print axioms step_129

theorem site_130 : EntryBinding.plan.code[130]? = some (6532, 3546349039) := rfl
theorem room_130 (initial : NativeState) : 130 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_130 : NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5 = 3546349039#32 := by decide
theorem step_130 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 130 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (130+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[130]'(room_130 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6532, 3546349039) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_130
  have pc : x.regs._PC = MemReloc.imageAddress base 6532 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    130 x inv.core (6532, 3546349039) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (130+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 130 + 4#64 = offset EntryBinding.plan (130+1) from by decide)
  have draws : DefaultState.drawsBefore initial 130 ≤ DefaultState.drawsBefore initial (130+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 130 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_130 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨(.lsr 32), [.reg (.x 15)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 15#5 15#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_130] using ob)
#print axioms site_130
#print axioms word_130
#print axioms step_130

theorem site_131 : EntryBinding.plan.code[131]? = some (6536, 2584674382) := rfl
theorem room_131 (initial : NativeState) : 131 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_131 : NativeEntryBodyDispatch.Adc64.selected 14#5 2#5 15#5 = 2584674382#32 := by decide
theorem step_131 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 131 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (131+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[131]'(room_131 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6536, 2584674382) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_131
  have pc : x.regs._PC = MemReloc.imageAddress base 6536 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    131 x inv.core (6536, 2584674382) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (131+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 131 + 4#64 = offset EntryBinding.plan (131+1) from by decide)
  have draws : DefaultState.drawsBefore initial 131 ≤ DefaultState.drawsBefore initial (131+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 131 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_131 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 14#5 2#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 14#5 2#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 14#5 2#5 15#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_131] using ob)
#print axioms site_131
#print axioms word_131
#print axioms step_131

theorem site_132 : EntryBinding.plan.code[132]? = some (6540, 2869100775) := rfl
theorem room_132 (initial : NativeState) : 132 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_132 : NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5 = 2869100775#32 := by decide
theorem step_132 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 132 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (132+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[132]'(room_132 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6540, 2869100775) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_132
  have pc : x.regs._PC = MemReloc.imageAddress base 6540 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    132 x inv.core (6540, 2869100775) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (132+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 132 + 4#64 = offset EntryBinding.plan (132+1) from by decide)
  have draws : DefaultState.drawsBefore initial 132 ≤ DefaultState.drawsBefore initial (132+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 132 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_132 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_132] using ob)
#print axioms site_132
#print axioms word_132
#print axioms step_132

theorem site_133 : EntryBinding.plan.code[133]? = some (6544, 3120824584) := rfl
theorem room_133 (initial : NativeState) : 133 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_133 : NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5 = 3120824584#32 := by decide
theorem step_133 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 133 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (133+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[133]'(room_133 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6544, 3120824584) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_133
  have pc : x.regs._PC = MemReloc.imageAddress base 6544 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    133 x inv.core (6544, 3120824584) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (133+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 133 + 4#64 = offset EntryBinding.plan (133+1) from by decide)
  have draws : DefaultState.drawsBefore initial 133 ≤ DefaultState.drawsBefore initial (133+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 133 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_133 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_133] using ob)
#print axioms site_133
#print axioms word_133
#print axioms step_133

theorem site_134 : EntryBinding.plan.code[134]? = some (6548, 3121283369) := rfl
theorem room_134 (initial : NativeState) : 134 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_134 : NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 11#5 = 3121283369#32 := by decide
theorem step_134 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 134 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (134+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[134]'(room_134 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6548, 3121283369) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_134
  have pc : x.regs._PC = MemReloc.imageAddress base 6548 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    134 x inv.core (6548, 3121283369) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (134+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 134 + 4#64 = offset EntryBinding.plan (134+1) from by decide)
  have draws : DefaultState.drawsBefore initial 134 ≤ DefaultState.drawsBefore initial (134+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 134 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_134 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 11#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 9#5 9#5 11#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_134] using ob)
#print axioms site_134
#print axioms word_134
#print axioms step_134

theorem site_135 : EntryBinding.plan.code[135]? = some (6552, 3121348938) := rfl
theorem room_135 (initial : NativeState) : 135 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_135 : NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 12#5 = 3121348938#32 := by decide
theorem step_135 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 135 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (135+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[135]'(room_135 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6552, 3121348938) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_135
  have pc : x.regs._PC = MemReloc.imageAddress base 6552 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    135 x inv.core (6552, 3121348938) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (135+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 135 + 4#64 = offset EntryBinding.plan (135+1) from by decide)
  have draws : DefaultState.drawsBefore initial 135 ≤ DefaultState.drawsBefore initial (135+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 135 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_135 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 12#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 10#5 10#5 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_135] using ob)
#print axioms site_135
#print axioms word_135
#print axioms step_135

theorem site_136 : EntryBinding.plan.code[136]? = some (6556, 2594125803) := rfl
theorem room_136 (initial : NativeState) : 136 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_136 : NativeEntryBodyDispatch.Csinc3.selected 11#5 = 2594125803#32 := by decide
theorem step_136 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 136 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (136+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[136]'(room_136 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6556, 2594125803) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_136
  have pc : x.regs._PC = MemReloc.imageAddress base 6556 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    136 x inv.core (6556, 2594125803) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (136+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 136 + 4#64 = offset EntryBinding.plan (136+1) from by decide)
  have draws : DefaultState.drawsBefore initial 136 ≤ DefaultState.drawsBefore initial (136+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 136 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_136 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Csinc3.selected 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Csinc3.tailX real x 11#5 (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_17 real x 11#5 (by decide) (by decide)) next (by simpa only [word_136] using ob)
#print axioms site_136
#print axioms word_136
#print axioms step_136

theorem site_137 : EntryBinding.plan.code[137]? = some (6560, 2869231880) := rfl
theorem room_137 (initial : NativeState) : 137 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_137 : NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 5#5 = 2869231880#32 := by decide
theorem step_137 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 137 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (137+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[137]'(room_137 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6560, 2869231880) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_137
  have pc : x.regs._PC = MemReloc.imageAddress base 6560 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    137 x inv.core (6560, 2869231880) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (137+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 137 + 4#64 = offset EntryBinding.plan (137+1) from by decide)
  have draws : DefaultState.drawsBefore initial 137 ≤ DefaultState.drawsBefore initial (137+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 137 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_137 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 8#5 8#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_137] using ob)
#print axioms site_137
#print axioms word_137
#print axioms step_137

theorem site_138 : EntryBinding.plan.code[138]? = some (6564, 3120955689) := rfl
theorem room_138 (initial : NativeState) : 138 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_138 : NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5 = 3120955689#32 := by decide
theorem step_138 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 138 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (138+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[138]'(room_138 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6564, 3120955689) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_138
  have pc : x.regs._PC = MemReloc.imageAddress base 6564 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    138 x inv.core (6564, 3120955689) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (138+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 138 + 4#64 = offset EntryBinding.plan (138+1) from by decide)
  have draws : DefaultState.drawsBefore initial 138 ≤ DefaultState.drawsBefore initial (138+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 138 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_138 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_138] using ob)
#print axioms site_138
#print axioms word_138
#print axioms step_138

theorem site_139 : EntryBinding.plan.code[139]? = some (6568, 3121414474) := rfl
theorem room_139 (initial : NativeState) : 139 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_139 : NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5 = 3121414474#32 := by decide
theorem step_139 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 139 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (139+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[139]'(room_139 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6568, 3121414474) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_139
  have pc : x.regs._PC = MemReloc.imageAddress base 6568 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    139 x inv.core (6568, 3121414474) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (139+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 139 + 4#64 = offset EntryBinding.plan (139+1) from by decide)
  have draws : DefaultState.drawsBefore initial 139 ≤ DefaultState.drawsBefore initial (139+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 139 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_139 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_139] using ob)
#print axioms site_139
#print axioms word_139
#print axioms step_139

theorem site_140 : EntryBinding.plan.code[140]? = some (6572, 2584609131) := rfl
theorem room_140 (initial : NativeState) : 140 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_140 : NativeEntryBodyDispatch.Adc64.selected 11#5 11#5 14#5 = 2584609131#32 := by decide
theorem step_140 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 140 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (140+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[140]'(room_140 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6572, 2584609131) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_140
  have pc : x.regs._PC = MemReloc.imageAddress base 6572 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    140 x inv.core (6572, 2584609131) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (140+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 140 + 4#64 = offset EntryBinding.plan (140+1) from by decide)
  have draws : DefaultState.drawsBefore initial 140 ≤ DefaultState.drawsBefore initial (140+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 140 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_140 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adc64.selected 11#5 11#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_140] using ob)
#print axioms site_140
#print axioms word_140
#print axioms step_140

theorem site_141 : EntryBinding.plan.code[141]? = some (6576, 2432697713) := rfl
theorem room_141 (initial : NativeState) : 141 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_141 : NativeEntryBodyDispatch.AddImm64.selected 17#5 11#5 1#12 = 2432697713#32 := by decide
theorem step_141 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 141 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (141+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[141]'(room_141 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6576, 2432697713) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_141
  have pc : x.regs._PC = MemReloc.imageAddress base 6576 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    141 x inv.core (6576, 2432697713) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (141+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 141 + 4#64 = offset EntryBinding.plan (141+1) from by decide)
  have draws : DefaultState.drawsBefore initial 141 ≤ DefaultState.drawsBefore initial (141+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 141 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_141 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddImm64.selected 17#5 11#5 1#12) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 17), some ⟨.add, [.reg (.x 11), .lit 1#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.AddImm64.tailX real x 17#5 11#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) (TranslateScalarTagCheck.Tails.tail_1 real x 17#5 11#5 1#12 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_141] using ob)
#print axioms site_141
#print axioms word_141
#print axioms step_141

theorem site_142 : EntryBinding.plan.code[142]? = some (6580, 2601614851) := rfl
theorem room_142 (initial : NativeState) : 142 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_142 : NativeEntryBodyDispatch.Madd64.selected 3#5 16#5 17#5 = 2601614851#32 := by decide
theorem step_142 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 142 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (142+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[142]'(room_142 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6580, 2601614851) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_142
  have pc : x.regs._PC = MemReloc.imageAddress base 6580 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    142 x inv.core (6580, 2601614851) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (142+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 142 + 4#64 = offset EntryBinding.plan (142+1) from by decide)
  have draws : DefaultState.drawsBefore initial 142 ≤ DefaultState.drawsBefore initial (142+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 142 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_142 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 3#5 16#5 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 16), .reg (.x 17)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 3#5 16#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 3#5 16#5 17#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_142] using ob)
#print axioms site_142
#print axioms word_142
#print axioms step_142

theorem site_143 : EntryBinding.plan.code[143]? = some (6584, 3546349092) := rfl
theorem room_143 (initial : NativeState) : 143 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_143 : NativeEntryBodyDispatch.SecpLsr32.selected 4#5 17#5 = 3546349092#32 := by decide
theorem step_143 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 143 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (143+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[143]'(room_143 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6584, 3546349092) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_143
  have pc : x.regs._PC = MemReloc.imageAddress base 6584 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    143 x inv.core (6584, 3546349092) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (143+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 143 + 4#64 = offset EntryBinding.plan (143+1) from by decide)
  have draws : DefaultState.drawsBefore initial 143 ≤ DefaultState.drawsBefore initial (143+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 143 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_143 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr32.selected 4#5 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨(.lsr 32), [.reg (.x 17)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 4#5 17#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 4#5 17#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_143] using ob)
#print axioms site_143
#print axioms word_143
#print axioms step_143

theorem site_144 : EntryBinding.plan.code[144]? = some (6588, 2870050915) := rfl
theorem room_144 (initial : NativeState) : 144 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_144 : N1D226.AddsShift64Generic.Encoding.selected 3#5 3#5 32#6 17#5 = 2870050915#32 := by decide
theorem step_144 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 144 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (144+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[144]'(room_144 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6588, 2870050915) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_144
  have pc : x.regs._PC = MemReloc.imageAddress base 6588 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    144 x inv.core (6588, 2870050915) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (144+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 144 + 4#64 = offset EntryBinding.plan (144+1) from by decide)
  have draws : DefaultState.drawsBefore initial 144 ≤ DefaultState.drawsBefore initial (144+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 144 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_144 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 3#5 3#5 32#6 17#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 3#5 3#5 32#6 17#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 3#5 32#6 17#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 3#5 3#5 32#6 17#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 3#5 3#5 32#6 17#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 3#5 3#5 32#6 17#5 vh, memory⟩)
    next (by simpa only [word_144] using ob)
#print axioms site_144
#print axioms word_144
#print axioms step_144

theorem site_145 : EntryBinding.plan.code[145]? = some (6592, 2583954404) := rfl
theorem room_145 (initial : NativeState) : 145 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_145 : N1D226.AdcZeroRn64Generic.Encoding.selected 4#5 4#5 = 2583954404#32 := by decide
theorem step_145 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 145 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (145+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[145]'(room_145 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6592, 2583954404) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_145
  have pc : x.regs._PC = MemReloc.imageAddress base 6592 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    145 x inv.core (6592, 2583954404) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (145+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 145 + 4#64 = offset EntryBinding.plan (145+1) from by decide)
  have draws : DefaultState.drawsBefore initial 145 ≤ DefaultState.drawsBefore initial (145+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 145 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_145 initial) compiles page (by decide)
    (N1D226.AdcZeroRn64Generic.Encoding.selected 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.lit 0#64, .reg (.x 4), .flag 2]⟩)] (none) (by rfl) x inv
    (N1D226.AdcZeroRn64Generic.Value.tailX real x 4#5 4#5 (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_13 real x 4#5 4#5 (by decide) (by decide)) next (by simpa only [word_145] using ob)
#print axioms site_145
#print axioms word_145
#print axioms step_145

theorem site_146 : EntryBinding.plan.code[146]? = some (6596, 2869100775) := rfl
theorem room_146 (initial : NativeState) : 146 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_146 : NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5 = 2869100775#32 := by decide
theorem step_146 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 146 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (146+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[146]'(room_146 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6596, 2869100775) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_146
  have pc : x.regs._PC = MemReloc.imageAddress base 6596 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    146 x inv.core (6596, 2869100775) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (146+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 146 + 4#64 = offset EntryBinding.plan (146+1) from by decide)
  have draws : DefaultState.drawsBefore initial 146 ≤ DefaultState.drawsBefore initial (146+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 146 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_146 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_146] using ob)
#print axioms site_146
#print axioms word_146
#print axioms step_146

theorem site_147 : EntryBinding.plan.code[147]? = some (6600, 3120824584) := rfl
theorem room_147 (initial : NativeState) : 147 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_147 : NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5 = 3120824584#32 := by decide
theorem step_147 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 147 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (147+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[147]'(room_147 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6600, 3120824584) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_147
  have pc : x.regs._PC = MemReloc.imageAddress base 6600 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    147 x inv.core (6600, 3120824584) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (147+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 147 + 4#64 = offset EntryBinding.plan (147+1) from by decide)
  have draws : DefaultState.drawsBefore initial 147 ≤ DefaultState.drawsBefore initial (147+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 147 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_147 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_147] using ob)
#print axioms site_147
#print axioms word_147
#print axioms step_147

theorem site_148 : EntryBinding.plan.code[148]? = some (6604, 3122594089) := rfl
theorem room_148 (initial : NativeState) : 148 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_148 : NativeEntryBodyDispatch.Adcs64ZRm.selected 9#5 9#5 = 3122594089#32 := by decide
theorem step_148 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 148 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (148+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[148]'(room_148 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6604, 3122594089) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_148
  have pc : x.regs._PC = MemReloc.imageAddress base 6604 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    148 x inv.core (6604, 3122594089) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (148+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 148 + 4#64 = offset EntryBinding.plan (148+1) from by decide)
  have draws : DefaultState.drawsBefore initial 148 ≤ DefaultState.drawsBefore initial (148+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 148 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_148 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 9#5 9#5 (by decide) (by decide) (by decide)) next (by simpa only [word_148] using ob)
#print axioms site_148
#print axioms word_148
#print axioms step_148

theorem site_149 : EntryBinding.plan.code[149]? = some (6608, 3122594122) := rfl
theorem room_149 (initial : NativeState) : 149 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_149 : NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5 = 3122594122#32 := by decide
theorem step_149 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 149 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (149+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[149]'(room_149 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6608, 3122594122) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_149
  have pc : x.regs._PC = MemReloc.imageAddress base 6608 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    149 x inv.core (6608, 3122594122) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (149+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 149 + 4#64 = offset EntryBinding.plan (149+1) from by decide)
  have draws : DefaultState.drawsBefore initial 149 ≤ DefaultState.drawsBefore initial (149+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 149 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_149 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 10#5 10#5 (by decide) (by decide) (by decide)) next (by simpa only [word_149] using ob)
#print axioms site_149
#print axioms word_149
#print axioms step_149

theorem site_150 : EntryBinding.plan.code[150]? = some (6612, 2594123809) := rfl
theorem room_150 (initial : NativeState) : 150 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_150 : NativeEntryBodyDispatch.Csel3.selected 1#5 1#5 = 2594123809#32 := by decide
theorem step_150 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 150 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (150+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[150]'(room_150 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6612, 2594123809) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_150
  have pc : x.regs._PC = MemReloc.imageAddress base 6612 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    150 x inv.core (6612, 2594123809) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (150+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 150 + 4#64 = offset EntryBinding.plan (150+1) from by decide)
  have draws : DefaultState.drawsBefore initial 150 ≤ DefaultState.drawsBefore initial (150+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 150 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_150 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Csel3.selected 1#5 1#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 1), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 1), .lit 0#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Csel3.tailX real x 1#5 1#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_16 real x 1#5 1#5 (by decide) (by decide) (by decide)) next (by simpa only [word_150] using ob)
#print axioms site_150
#print axioms word_150
#print axioms step_150

theorem site_151 : EntryBinding.plan.code[151]? = some (6616, 3942711527) := rfl
theorem room_151 (initial : NativeState) : 151 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_151 : NativeEntryBodyDispatch.SubsShift64.selected 7#5 7#5 0#6 1#5 = 3942711527#32 := by decide
theorem step_151 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 151 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (151+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[151]'(room_151 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6616, 3942711527) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_151
  have pc : x.regs._PC = MemReloc.imageAddress base 6616 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    151 x inv.core (6616, 3942711527) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (151+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 151 + 4#64 = offset EntryBinding.plan (151+1) from by decide)
  have draws : DefaultState.drawsBefore initial 151 ≤ DefaultState.drawsBefore initial (151+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 151 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_151 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 7#5 7#5 0#6 1#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.sbc3, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 7#5 7#5 0#6 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 7#5 7#5 0#6 1#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_151] using ob)
#print axioms site_151
#print axioms word_151
#print axioms step_151

theorem site_152 : EntryBinding.plan.code[152]? = some (6620, 4196335880) := rfl
theorem room_152 (initial : NativeState) : 152 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_152 : NativeEntryBodyDispatch.Sbcs64.selected 8#5 8#5 = 4196335880#32 := by decide
theorem step_152 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 152 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (152+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[152]'(room_152 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6620, 4196335880) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_152
  have pc : x.regs._PC = MemReloc.imageAddress base 6620 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    152 x inv.core (6620, 4196335880) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (152+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 152 + 4#64 = offset EntryBinding.plan (152+1) from by decide)
  have draws : DefaultState.drawsBefore initial 152 ≤ DefaultState.drawsBefore initial (152+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 152 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_152 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64.selected 8#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.sbc3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 8), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64.tailX real x 8#5 8#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_18 real x 8#5 8#5 (by decide) (by decide) (by decide)) next (by simpa only [word_152] using ob)
#print axioms site_152
#print axioms word_152
#print axioms step_152

theorem site_153 : EntryBinding.plan.code[153]? = some (6624, 4196335913) := rfl
theorem room_153 (initial : NativeState) : 153 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_153 : NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5 = 4196335913#32 := by decide
theorem step_153 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 153 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (153+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[153]'(room_153 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6624, 4196335913) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_153
  have pc : x.regs._PC = MemReloc.imageAddress base 6624 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    153 x inv.core (6624, 4196335913) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (153+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 153 + 4#64 = offset EntryBinding.plan (153+1) from by decide)
  have draws : DefaultState.drawsBefore initial 153 ≤ DefaultState.drawsBefore initial (153+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 153 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_153 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.sbc3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_18 real x 9#5 9#5 (by decide) (by decide) (by decide)) next (by simpa only [word_153] using ob)
#print axioms site_153
#print axioms word_153
#print axioms step_153

theorem site_154 : EntryBinding.plan.code[154]? = some (6628, 3659465034) := rfl
theorem room_154 (initial : NativeState) : 154 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_154 : NativeEntryBodyDispatch.Sbc64.selected 10#5 10#5 = 3659465034#32 := by decide
theorem step_154 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 154 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (154+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[154]'(room_154 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (6628, 3659465034) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_154
  have pc : x.regs._PC = MemReloc.imageAddress base 6628 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    154 x inv.core (6628, 3659465034) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (154+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 154 + 4#64 = offset EntryBinding.plan (154+1) from by decide)
  have draws : DefaultState.drawsBefore initial 154 ≤ DefaultState.drawsBefore initial (154+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 154 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_154 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbc64.selected 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Sbc64.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_7 real x 10#5 10#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_154] using ob)
#print axioms site_154
#print axioms word_154
#print axioms step_154

theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (k : Nat) (room : k < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length)
    (selected : k ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 52, 53, 54, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154] : List Nat))
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'room) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_2 real raw config rows mapping base initial topology layout page x inv
  · exact step_3 real raw config rows mapping base initial topology layout page x inv
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
  · exact step_52 real raw config rows mapping base initial topology layout page x inv
  · exact step_53 real raw config rows mapping base initial topology layout page x inv
  · exact step_54 real raw config rows mapping base initial topology layout page x inv
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
  · exact step_76 real raw config rows mapping base initial topology layout page x inv
  · exact step_77 real raw config rows mapping base initial topology layout page x inv
  · exact step_78 real raw config rows mapping base initial topology layout page x inv
  · exact step_79 real raw config rows mapping base initial topology layout page x inv
  · exact step_80 real raw config rows mapping base initial topology layout page x inv
  · exact step_81 real raw config rows mapping base initial topology layout page x inv
  · exact step_82 real raw config rows mapping base initial topology layout page x inv
  · exact step_83 real raw config rows mapping base initial topology layout page x inv
  · exact step_84 real raw config rows mapping base initial topology layout page x inv
  · exact step_85 real raw config rows mapping base initial topology layout page x inv
  · exact step_86 real raw config rows mapping base initial topology layout page x inv
  · exact step_87 real raw config rows mapping base initial topology layout page x inv
  · exact step_88 real raw config rows mapping base initial topology layout page x inv
  · exact step_89 real raw config rows mapping base initial topology layout page x inv
  · exact step_90 real raw config rows mapping base initial topology layout page x inv
  · exact step_91 real raw config rows mapping base initial topology layout page x inv
  · exact step_92 real raw config rows mapping base initial topology layout page x inv
  · exact step_93 real raw config rows mapping base initial topology layout page x inv
  · exact step_94 real raw config rows mapping base initial topology layout page x inv
  · exact step_95 real raw config rows mapping base initial topology layout page x inv
  · exact step_96 real raw config rows mapping base initial topology layout page x inv
  · exact step_97 real raw config rows mapping base initial topology layout page x inv
  · exact step_98 real raw config rows mapping base initial topology layout page x inv
  · exact step_99 real raw config rows mapping base initial topology layout page x inv
  · exact step_100 real raw config rows mapping base initial topology layout page x inv
  · exact step_101 real raw config rows mapping base initial topology layout page x inv
  · exact step_102 real raw config rows mapping base initial topology layout page x inv
  · exact step_103 real raw config rows mapping base initial topology layout page x inv
  · exact step_104 real raw config rows mapping base initial topology layout page x inv
  · exact step_105 real raw config rows mapping base initial topology layout page x inv
  · exact step_106 real raw config rows mapping base initial topology layout page x inv
  · exact step_107 real raw config rows mapping base initial topology layout page x inv
  · exact step_108 real raw config rows mapping base initial topology layout page x inv
  · exact step_109 real raw config rows mapping base initial topology layout page x inv
  · exact step_110 real raw config rows mapping base initial topology layout page x inv
  · exact step_111 real raw config rows mapping base initial topology layout page x inv
  · exact step_112 real raw config rows mapping base initial topology layout page x inv
  · exact step_113 real raw config rows mapping base initial topology layout page x inv
  · exact step_114 real raw config rows mapping base initial topology layout page x inv
  · exact step_115 real raw config rows mapping base initial topology layout page x inv
  · exact step_116 real raw config rows mapping base initial topology layout page x inv
  · exact step_117 real raw config rows mapping base initial topology layout page x inv
  · exact step_118 real raw config rows mapping base initial topology layout page x inv
  · exact step_119 real raw config rows mapping base initial topology layout page x inv
  · exact step_120 real raw config rows mapping base initial topology layout page x inv
  · exact step_121 real raw config rows mapping base initial topology layout page x inv
  · exact step_122 real raw config rows mapping base initial topology layout page x inv
  · exact step_123 real raw config rows mapping base initial topology layout page x inv
  · exact step_124 real raw config rows mapping base initial topology layout page x inv
  · exact step_125 real raw config rows mapping base initial topology layout page x inv
  · exact step_126 real raw config rows mapping base initial topology layout page x inv
  · exact step_127 real raw config rows mapping base initial topology layout page x inv
  · exact step_128 real raw config rows mapping base initial topology layout page x inv
  · exact step_129 real raw config rows mapping base initial topology layout page x inv
  · exact step_130 real raw config rows mapping base initial topology layout page x inv
  · exact step_131 real raw config rows mapping base initial topology layout page x inv
  · exact step_132 real raw config rows mapping base initial topology layout page x inv
  · exact step_133 real raw config rows mapping base initial topology layout page x inv
  · exact step_134 real raw config rows mapping base initial topology layout page x inv
  · exact step_135 real raw config rows mapping base initial topology layout page x inv
  · exact step_136 real raw config rows mapping base initial topology layout page x inv
  · exact step_137 real raw config rows mapping base initial topology layout page x inv
  · exact step_138 real raw config rows mapping base initial topology layout page x inv
  · exact step_139 real raw config rows mapping base initial topology layout page x inv
  · exact step_140 real raw config rows mapping base initial topology layout page x inv
  · exact step_141 real raw config rows mapping base initial topology layout page x inv
  · exact step_142 real raw config rows mapping base initial topology layout page x inv
  · exact step_143 real raw config rows mapping base initial topology layout page x inv
  · exact step_144 real raw config rows mapping base initial topology layout page x inv
  · exact step_145 real raw config rows mapping base initial topology layout page x inv
  · exact step_146 real raw config rows mapping base initial topology layout page x inv
  · exact step_147 real raw config rows mapping base initial topology layout page x inv
  · exact step_148 real raw config rows mapping base initial topology layout page x inv
  · exact step_149 real raw config rows mapping base initial topology layout page x inv
  · exact step_150 real raw config rows mapping base initial topology layout page x inv
  · exact step_151 real raw config rows mapping base initial topology layout page x inv
  · exact step_152 real raw config rows mapping base initial topology layout page x inv
  · exact step_153 real raw config rows mapping base initial topology layout page x inv
  · exact step_154 real raw config rows mapping base initial topology layout page x inv
#print axioms all_steps

end PipeLean_D234_SecpMul_c17.DitBodyScalar
