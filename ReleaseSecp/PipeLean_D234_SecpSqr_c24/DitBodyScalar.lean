import PipeLean_D234_SecpSqr_c24.DitBodyState
import DitShim243.RawFetch
import PipeLean_D234_SecpSqr_c24.DefaultState
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
import ArmCertValueTail.SecpLsr31
import ArmCertValueTail.SecpLsr32
import ArmCertValueTail.SecpSbc64
import ArmCertValueTail.SubsShift64
import ArmCertValueTail.Umulh64
import N1D226.AdcZeroRn64Generic.Value
import N1D226.AddsShift64Generic.Value
import N1D226.Madd64Generic.DriverValue
import N1D226.Umaddl64Generic.DriverValue
import TranslateScalarTagCheck.Runtime
import TranslateScalarTagCheck.Secp
import TranslateScalarTagCheck.Tails
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
namespace PipeLean_D234_SecpSqr_c24.DitBodyScalar

theorem site_2 : EntryBinding.plan.code[2]? = some (7056, 2611641666) := rfl
theorem room_2 (initial : NativeState) : 2 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_2 : N1D226.Umaddl64Generic.Encoding.selected 2#5 10#5 10#5 = 2611641666#32 := by decide
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
  have member : (7056, 2611641666) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 7056 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (7056, 2611641666) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (2+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 2 + 4#64 = offset EntryBinding.plan (2+1) from by decide)
  have draws : DefaultState.drawsBefore initial 2 ≤ DefaultState.drawsBefore initial (2+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 2 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_2 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 2#5 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 2#5 10#5 10#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 2#5 10#5 10#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 2#5 10#5 10#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 2#5 10#5 10#5 vh, memory⟩)
    next (by simpa only [word_2] using ob)
#print axioms site_2
#print axioms word_2
#print axioms step_2

theorem site_3 : EntryBinding.plan.code[3]? = some (7060, 3546348878) := rfl
theorem room_3 (initial : NativeState) : 3 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_3 : NativeEntryBodyDispatch.SecpLsr32.selected 14#5 10#5 = 3546348878#32 := by decide
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
  have member : (7060, 3546348878) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 7060 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (7060, 3546348878) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 10)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 14#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 14#5 10#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_3] using ob)
#print axioms site_3
#print axioms word_3
#print axioms step_3

theorem site_4 : EntryBinding.plan.code[4]? = some (7064, 2611903939) := rfl
theorem room_4 (initial : NativeState) : 4 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_4 : N1D226.Umaddl64Generic.Encoding.selected 3#5 14#5 14#5 = 2611903939#32 := by decide
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
  have member : (7064, 2611903939) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 7064 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (7064, 2611903939) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (4+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 4 + 4#64 = offset EntryBinding.plan (4+1) from by decide)
  have draws : DefaultState.drawsBefore initial 4 ≤ DefaultState.drawsBefore initial (4+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 4 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_4 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 3#5 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 3#5 14#5 14#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 3#5 14#5 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 3#5 14#5 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 3#5 14#5 14#5 vh, memory⟩)
    next (by simpa only [word_4] using ob)
#print axioms site_4
#print axioms word_4
#print axioms step_4

theorem site_5 : EntryBinding.plan.code[5]? = some (7068, 2611903822) := rfl
theorem room_5 (initial : NativeState) : 5 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_5 : N1D226.Umaddl64Generic.Encoding.selected 14#5 10#5 14#5 = 2611903822#32 := by decide
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
  have member : (7068, 2611903822) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 7068 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (7068, 2611903822) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (5+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 5 + 4#64 = offset EntryBinding.plan (5+1) from by decide)
  have draws : DefaultState.drawsBefore initial 5 ≤ DefaultState.drawsBefore initial (5+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 5 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_5 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 14#5 10#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 10#5 14#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 10#5 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 14#5 10#5 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 14#5 10#5 14#5 vh, memory⟩)
    next (by simpa only [word_5] using ob)
#print axioms site_5
#print axioms word_5
#print axioms step_5

theorem site_6 : EntryBinding.plan.code[6]? = some (7072, 2869855298) := rfl
theorem room_6 (initial : NativeState) : 6 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_6 : N1D226.AddsShift64Generic.Encoding.selected 2#5 2#5 33#6 14#5 = 2869855298#32 := by decide
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
  have member : (7072, 2869855298) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 7072 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (7072, 2869855298) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (6+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 6 + 4#64 = offset EntryBinding.plan (6+1) from by decide)
  have draws : DefaultState.drawsBefore initial 6 ≤ DefaultState.drawsBefore initial (6+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 6 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_6 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 2#5 2#5 33#6 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 2#5 2#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 2#5 33#6 14#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 2#5 2#5 33#6 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 2#5 2#5 33#6 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 2#5 2#5 33#6 14#5 vh, memory⟩)
    next (by simpa only [word_6] using ob)
#print axioms site_6
#print axioms word_6
#print axioms step_6

theorem site_7 : EntryBinding.plan.code[7]? = some (7076, 3546283470) := rfl
theorem room_7 (initial : NativeState) : 7 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_7 : NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5 = 3546283470#32 := by decide
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
  have member : (7076, 3546283470) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 7076 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (7076, 3546283470) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (7+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 7 + 4#64 = offset EntryBinding.plan (7+1) from by decide)
  have draws : DefaultState.drawsBefore initial 7 ≤ DefaultState.drawsBefore initial (7+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 7 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_7 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_4 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_7] using ob)
#print axioms site_7
#print axioms word_7
#print axioms step_7

theorem site_8 : EntryBinding.plan.code[8]? = some (7080, 2584608867) := rfl
theorem room_8 (initial : NativeState) : 8 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_8 : NativeEntryBodyDispatch.Adc64.selected 3#5 3#5 14#5 = 2584608867#32 := by decide
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
  have member : (7080, 2584608867) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 7080 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (7080, 2584608867) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 3#5 3#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 14), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 3#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 3#5 3#5 14#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_8] using ob)
#print axioms site_8
#print axioms word_8
#print axioms step_8

theorem site_9 : EntryBinding.plan.code[9]? = some (7084, 2611707236) := rfl
theorem room_9 (initial : NativeState) : 9 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_9 : N1D226.Umaddl64Generic.Encoding.selected 4#5 11#5 11#5 = 2611707236#32 := by decide
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
  have member : (7084, 2611707236) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 7084 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (7084, 2611707236) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (9+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 9 + 4#64 = offset EntryBinding.plan (9+1) from by decide)
  have draws : DefaultState.drawsBefore initial 9 ≤ DefaultState.drawsBefore initial (9+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 9 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_9 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 4#5 11#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 4#5 11#5 11#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 4#5 11#5 11#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 4#5 11#5 11#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 4#5 11#5 11#5 vh, memory⟩)
    next (by simpa only [word_9] using ob)
#print axioms site_9
#print axioms word_9
#print axioms step_9

theorem site_10 : EntryBinding.plan.code[10]? = some (7088, 3546348910) := rfl
theorem room_10 (initial : NativeState) : 10 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_10 : NativeEntryBodyDispatch.SecpLsr32.selected 14#5 11#5 = 3546348910#32 := by decide
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
  have member : (7088, 3546348910) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 7088 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (7088, 3546348910) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 11)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 14#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 14#5 11#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_10] using ob)
#print axioms site_10
#print axioms word_10
#print axioms step_10

theorem site_11 : EntryBinding.plan.code[11]? = some (7092, 2611903941) := rfl
theorem room_11 (initial : NativeState) : 11 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_11 : N1D226.Umaddl64Generic.Encoding.selected 5#5 14#5 14#5 = 2611903941#32 := by decide
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
  have member : (7092, 2611903941) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 7092 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (7092, 2611903941) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (11+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 11 + 4#64 = offset EntryBinding.plan (11+1) from by decide)
  have draws : DefaultState.drawsBefore initial 11 ≤ DefaultState.drawsBefore initial (11+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 11 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_11 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 5#5 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 14#5 14#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 14#5 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 5#5 14#5 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 5#5 14#5 14#5 vh, memory⟩)
    next (by simpa only [word_11] using ob)
#print axioms site_11
#print axioms word_11
#print axioms step_11

theorem site_12 : EntryBinding.plan.code[12]? = some (7096, 2611903854) := rfl
theorem room_12 (initial : NativeState) : 12 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_12 : N1D226.Umaddl64Generic.Encoding.selected 14#5 11#5 14#5 = 2611903854#32 := by decide
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
  have member : (7096, 2611903854) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 7096 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (7096, 2611903854) member pc
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
    (N1D226.Umaddl64Generic.Encoding.selected 14#5 11#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 11#5 14#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 11#5 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 14#5 11#5 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 14#5 11#5 14#5 vh, memory⟩)
    next (by simpa only [word_12] using ob)
#print axioms site_12
#print axioms word_12
#print axioms step_12

theorem site_13 : EntryBinding.plan.code[13]? = some (7100, 2601221455) := rfl
theorem room_13 (initial : NativeState) : 13 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_13 : NativeEntryBodyDispatch.Madd64.selected 15#5 10#5 11#5 = 2601221455#32 := by decide
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
  have member : (7100, 2601221455) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 7100 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (7100, 2601221455) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (13+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 13 + 4#64 = offset EntryBinding.plan (13+1) from by decide)
  have draws : DefaultState.drawsBefore initial 13 ≤ DefaultState.drawsBefore initial (13+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 13 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_13 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 15#5 10#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 10), .reg (.x 11)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 15#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 15#5 10#5 11#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_13] using ob)
#print axioms site_13
#print axioms word_13
#print axioms step_13

theorem site_14 : EntryBinding.plan.code[14]? = some (7104, 2613804368) := rfl
theorem room_14 (initial : NativeState) : 14 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_14 : NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5 = 2613804368#32 := by decide
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
  have member : (7104, 2613804368) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 7104 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (7104, 2613804368) member pc
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
    (NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 10), .reg (.x 11)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_14] using ob)
#print axioms site_14
#print axioms word_14
#print axioms step_14

theorem site_15 : EntryBinding.plan.code[15]? = some (7108, 2869855364) := rfl
theorem room_15 (initial : NativeState) : 15 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_15 : N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 33#6 14#5 = 2869855364#32 := by decide
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
  have member : (7108, 2869855364) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_15
  have pc : x.regs._PC = MemReloc.imageAddress base 7108 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (7108, 2869855364) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (15+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 15 + 4#64 = offset EntryBinding.plan (15+1) from by decide)
  have draws : DefaultState.drawsBefore initial 15 ≤ DefaultState.drawsBefore initial (15+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 15 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_15 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 33#6 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 4#5 4#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 4#5 33#6 14#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 4#5 4#5 33#6 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 4#5 4#5 33#6 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 4#5 4#5 33#6 14#5 vh, memory⟩)
    next (by simpa only [word_15] using ob)
#print axioms site_15
#print axioms word_15
#print axioms step_15

theorem site_16 : EntryBinding.plan.code[16]? = some (7112, 3546283470) := rfl
theorem room_16 (initial : NativeState) : 16 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_16 : NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5 = 3546283470#32 := by decide
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
  have member : (7112, 3546283470) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 7112 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (7112, 3546283470) member pc
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
    (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_4 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_16] using ob)
#print axioms site_16
#print axioms word_16
#print axioms step_16

theorem site_17 : EntryBinding.plan.code[17]? = some (7116, 2584608933) := rfl
theorem room_17 (initial : NativeState) : 17 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_17 : NativeEntryBodyDispatch.Adc64.selected 5#5 5#5 14#5 = 2584608933#32 := by decide
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
  have member : (7116, 2584608933) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 7116 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (7116, 2584608933) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 5#5 5#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 14), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 5#5 5#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 5#5 5#5 14#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_17] using ob)
#print axioms site_17
#print axioms word_17
#print axioms step_17

theorem site_18 : EntryBinding.plan.code[18]? = some (7120, 2869887471) := rfl
theorem room_18 (initial : NativeState) : 18 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_18 : NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5 = 2869887471#32 := by decide
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
  have member : (7120, 2869887471) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 7120 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (7120, 2869887471) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_18] using ob)
#print axioms site_18
#print axioms word_18
#print axioms step_18

theorem site_19 : EntryBinding.plan.code[19]? = some (7124, 3121611280) := rfl
theorem room_19 (initial : NativeState) : 19 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_19 : NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5 = 3121611280#32 := by decide
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
  have member : (7124, 3121611280) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 7124 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (7124, 3121611280) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_19] using ob)
#print axioms site_19
#print axioms word_19
#print axioms step_19

theorem site_20 : EntryBinding.plan.code[20]? = some (7128, 2585723045) := rfl
theorem room_20 (initial : NativeState) : 20 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_20 : NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5 = 2585723045#32 := by decide
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
  have member : (7128, 2585723045) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 7128 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (7128, 2585723045) member pc
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
    (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 5#5 5#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_20] using ob)
#print axioms site_20
#print axioms word_20
#print axioms step_20

theorem site_21 : EntryBinding.plan.code[21]? = some (7132, 2869887075) := rfl
theorem room_21 (initial : NativeState) : 21 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_21 : NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 15#5 = 2869887075#32 := by decide
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
  have member : (7132, 2869887075) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 7132 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (7132, 2869887075) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_21] using ob)
#print axioms site_21
#print axioms word_21
#print axioms step_21

theorem site_22 : EntryBinding.plan.code[22]? = some (7136, 3121610884) := rfl
theorem room_22 (initial : NativeState) : 22 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_22 : NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 16#5 = 3121610884#32 := by decide
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
  have member : (7136, 3121610884) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 7136 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (7136, 3121610884) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_22] using ob)
#print axioms site_22
#print axioms word_22
#print axioms step_22

theorem site_23 : EntryBinding.plan.code[23]? = some (7140, 2585723045) := rfl
theorem room_23 (initial : NativeState) : 23 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_23 : NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5 = 2585723045#32 := by decide
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
  have member : (7140, 2585723045) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 7140 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (7140, 2585723045) member pc
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
    (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 5#5 5#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_23] using ob)
#print axioms site_23
#print axioms word_23
#print axioms step_23

theorem site_24 : EntryBinding.plan.code[24]? = some (7144, 2611772806) := rfl
theorem room_24 (initial : NativeState) : 24 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_24 : N1D226.Umaddl64Generic.Encoding.selected 6#5 12#5 12#5 = 2611772806#32 := by decide
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
  have member : (7144, 2611772806) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 7144 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (7144, 2611772806) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (24+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 24 + 4#64 = offset EntryBinding.plan (24+1) from by decide)
  have draws : DefaultState.drawsBefore initial 24 ≤ DefaultState.drawsBefore initial (24+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 24 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_24 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 6#5 12#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 6#5 12#5 12#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 6#5 12#5 12#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 6#5 12#5 12#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 6#5 12#5 12#5 vh, memory⟩)
    next (by simpa only [word_24] using ob)
#print axioms site_24
#print axioms word_24
#print axioms step_24

theorem site_25 : EntryBinding.plan.code[25]? = some (7148, 3546348942) := rfl
theorem room_25 (initial : NativeState) : 25 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_25 : NativeEntryBodyDispatch.SecpLsr32.selected 14#5 12#5 = 3546348942#32 := by decide
theorem step_25 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 25 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (25+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[25]'(room_25 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7148, 3546348942) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_25
  have pc : x.regs._PC = MemReloc.imageAddress base 7148 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    25 x inv.core (7148, 3546348942) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (25+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 25 + 4#64 = offset EntryBinding.plan (25+1) from by decide)
  have draws : DefaultState.drawsBefore initial 25 ≤ DefaultState.drawsBefore initial (25+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 25 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_25 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 12)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 14#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 14#5 12#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_25] using ob)
#print axioms site_25
#print axioms word_25
#print axioms step_25

theorem site_26 : EntryBinding.plan.code[26]? = some (7152, 2611903943) := rfl
theorem room_26 (initial : NativeState) : 26 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_26 : N1D226.Umaddl64Generic.Encoding.selected 7#5 14#5 14#5 = 2611903943#32 := by decide
theorem step_26 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 26 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (26+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[26]'(room_26 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7152, 2611903943) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_26
  have pc : x.regs._PC = MemReloc.imageAddress base 7152 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    26 x inv.core (7152, 2611903943) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (26+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 26 + 4#64 = offset EntryBinding.plan (26+1) from by decide)
  have draws : DefaultState.drawsBefore initial 26 ≤ DefaultState.drawsBefore initial (26+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 26 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_26 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 7#5 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 7#5 14#5 14#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 7#5 14#5 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 7#5 14#5 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 7#5 14#5 14#5 vh, memory⟩)
    next (by simpa only [word_26] using ob)
#print axioms site_26
#print axioms word_26
#print axioms step_26

theorem site_27 : EntryBinding.plan.code[27]? = some (7156, 2611903886) := rfl
theorem room_27 (initial : NativeState) : 27 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_27 : N1D226.Umaddl64Generic.Encoding.selected 14#5 12#5 14#5 = 2611903886#32 := by decide
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
  have member : (7156, 2611903886) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 7156 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (7156, 2611903886) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (27+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 27 + 4#64 = offset EntryBinding.plan (27+1) from by decide)
  have draws : DefaultState.drawsBefore initial 27 ≤ DefaultState.drawsBefore initial (27+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 27 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_27 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 14#5 12#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 12#5 14#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 12#5 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 14#5 12#5 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 14#5 12#5 14#5 vh, memory⟩)
    next (by simpa only [word_27] using ob)
#print axioms site_27
#print axioms word_27
#print axioms step_27

theorem site_28 : EntryBinding.plan.code[28]? = some (7160, 2869855430) := rfl
theorem room_28 (initial : NativeState) : 28 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_28 : N1D226.AddsShift64Generic.Encoding.selected 6#5 6#5 33#6 14#5 = 2869855430#32 := by decide
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
  have member : (7160, 2869855430) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_28
  have pc : x.regs._PC = MemReloc.imageAddress base 7160 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    28 x inv.core (7160, 2869855430) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (28+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 28 + 4#64 = offset EntryBinding.plan (28+1) from by decide)
  have draws : DefaultState.drawsBefore initial 28 ≤ DefaultState.drawsBefore initial (28+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 28 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_28 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 6#5 6#5 33#6 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 6#5 6#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 6#5 33#6 14#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 6#5 6#5 33#6 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 6#5 6#5 33#6 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 6#5 6#5 33#6 14#5 vh, memory⟩)
    next (by simpa only [word_28] using ob)
#print axioms site_28
#print axioms word_28
#print axioms step_28

theorem site_29 : EntryBinding.plan.code[29]? = some (7164, 3546283470) := rfl
theorem room_29 (initial : NativeState) : 29 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_29 : NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5 = 3546283470#32 := by decide
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
  have member : (7164, 3546283470) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_29
  have pc : x.regs._PC = MemReloc.imageAddress base 7164 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    29 x inv.core (7164, 3546283470) member pc
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
    (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_4 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_29] using ob)
#print axioms site_29
#print axioms word_29
#print axioms step_29

theorem site_30 : EntryBinding.plan.code[30]? = some (7168, 2584608999) := rfl
theorem room_30 (initial : NativeState) : 30 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_30 : NativeEntryBodyDispatch.Adc64.selected 7#5 7#5 14#5 = 2584608999#32 := by decide
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
  have member : (7168, 2584608999) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_30
  have pc : x.regs._PC = MemReloc.imageAddress base 7168 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    30 x inv.core (7168, 2584608999) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 7#5 7#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_30] using ob)
#print axioms site_30
#print axioms word_30
#print axioms step_30

theorem site_31 : EntryBinding.plan.code[31]? = some (7172, 2611838376) := rfl
theorem room_31 (initial : NativeState) : 31 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_31 : N1D226.Umaddl64Generic.Encoding.selected 8#5 13#5 13#5 = 2611838376#32 := by decide
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
  have member : (7172, 2611838376) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_31
  have pc : x.regs._PC = MemReloc.imageAddress base 7172 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    31 x inv.core (7172, 2611838376) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (31+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 31 + 4#64 = offset EntryBinding.plan (31+1) from by decide)
  have draws : DefaultState.drawsBefore initial 31 ≤ DefaultState.drawsBefore initial (31+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 31 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_31 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 8#5 13#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 8#5 13#5 13#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 8#5 13#5 13#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 8#5 13#5 13#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 8#5 13#5 13#5 vh, memory⟩)
    next (by simpa only [word_31] using ob)
#print axioms site_31
#print axioms word_31
#print axioms step_31

theorem site_32 : EntryBinding.plan.code[32]? = some (7176, 3546348974) := rfl
theorem room_32 (initial : NativeState) : 32 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_32 : NativeEntryBodyDispatch.SecpLsr32.selected 14#5 13#5 = 3546348974#32 := by decide
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
  have member : (7176, 3546348974) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_32
  have pc : x.regs._PC = MemReloc.imageAddress base 7176 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    32 x inv.core (7176, 3546348974) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (32+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 32 + 4#64 = offset EntryBinding.plan (32+1) from by decide)
  have draws : DefaultState.drawsBefore initial 32 ≤ DefaultState.drawsBefore initial (32+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 32 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_32 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 13)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 14#5 13#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 14#5 13#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_32] using ob)
#print axioms site_32
#print axioms word_32
#print axioms step_32

theorem site_33 : EntryBinding.plan.code[33]? = some (7180, 2611903945) := rfl
theorem room_33 (initial : NativeState) : 33 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_33 : N1D226.Umaddl64Generic.Encoding.selected 9#5 14#5 14#5 = 2611903945#32 := by decide
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
  have member : (7180, 2611903945) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_33
  have pc : x.regs._PC = MemReloc.imageAddress base 7180 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    33 x inv.core (7180, 2611903945) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (33+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 33 + 4#64 = offset EntryBinding.plan (33+1) from by decide)
  have draws : DefaultState.drawsBefore initial 33 ≤ DefaultState.drawsBefore initial (33+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 33 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_33 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 9#5 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 9#5 14#5 14#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 9#5 14#5 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 9#5 14#5 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 9#5 14#5 14#5 vh, memory⟩)
    next (by simpa only [word_33] using ob)
#print axioms site_33
#print axioms word_33
#print axioms step_33

theorem site_34 : EntryBinding.plan.code[34]? = some (7184, 2611903918) := rfl
theorem room_34 (initial : NativeState) : 34 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_34 : N1D226.Umaddl64Generic.Encoding.selected 14#5 13#5 14#5 = 2611903918#32 := by decide
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
  have member : (7184, 2611903918) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_34
  have pc : x.regs._PC = MemReloc.imageAddress base 7184 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    34 x inv.core (7184, 2611903918) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (34+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 34 + 4#64 = offset EntryBinding.plan (34+1) from by decide)
  have draws : DefaultState.drawsBefore initial 34 ≤ DefaultState.drawsBefore initial (34+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 34 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_34 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 14#5 13#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 13#5 14#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 13#5 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 14#5 13#5 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 14#5 13#5 14#5 vh, memory⟩)
    next (by simpa only [word_34] using ob)
#print axioms site_34
#print axioms word_34
#print axioms step_34

theorem site_35 : EntryBinding.plan.code[35]? = some (7188, 2601352591) := rfl
theorem room_35 (initial : NativeState) : 35 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_35 : NativeEntryBodyDispatch.Madd64.selected 15#5 12#5 13#5 = 2601352591#32 := by decide
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
  have member : (7188, 2601352591) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_35
  have pc : x.regs._PC = MemReloc.imageAddress base 7188 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    35 x inv.core (7188, 2601352591) member pc
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
    (NativeEntryBodyDispatch.Madd64.selected 15#5 12#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 12), .reg (.x 13)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 15#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 15#5 12#5 13#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_35] using ob)
#print axioms site_35
#print axioms word_35
#print axioms step_35

theorem site_36 : EntryBinding.plan.code[36]? = some (7192, 2613935504) := rfl
theorem room_36 (initial : NativeState) : 36 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_36 : NativeEntryBodyDispatch.Umulh64.selected 16#5 12#5 13#5 = 2613935504#32 := by decide
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
  have member : (7192, 2613935504) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_36
  have pc : x.regs._PC = MemReloc.imageAddress base 7192 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    36 x inv.core (7192, 2613935504) member pc
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
    (NativeEntryBodyDispatch.Umulh64.selected 16#5 12#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 12), .reg (.x 13)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 16#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 16#5 12#5 13#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_36] using ob)
#print axioms site_36
#print axioms word_36
#print axioms step_36

theorem site_37 : EntryBinding.plan.code[37]? = some (7196, 2869855496) := rfl
theorem room_37 (initial : NativeState) : 37 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_37 : N1D226.AddsShift64Generic.Encoding.selected 8#5 8#5 33#6 14#5 = 2869855496#32 := by decide
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
  have member : (7196, 2869855496) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_37
  have pc : x.regs._PC = MemReloc.imageAddress base 7196 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    37 x inv.core (7196, 2869855496) member pc
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
    (N1D226.AddsShift64Generic.Encoding.selected 8#5 8#5 33#6 14#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 8#5 8#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 8#5 33#6 14#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 8#5 8#5 33#6 14#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 8#5 8#5 33#6 14#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 8#5 8#5 33#6 14#5 vh, memory⟩)
    next (by simpa only [word_37] using ob)
#print axioms site_37
#print axioms word_37
#print axioms step_37

theorem site_38 : EntryBinding.plan.code[38]? = some (7200, 3546283470) := rfl
theorem room_38 (initial : NativeState) : 38 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_38 : NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5 = 3546283470#32 := by decide
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
  have member : (7200, 3546283470) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_38
  have pc : x.regs._PC = MemReloc.imageAddress base 7200 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    38 x inv.core (7200, 3546283470) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (38+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 38 + 4#64 = offset EntryBinding.plan (38+1) from by decide)
  have draws : DefaultState.drawsBefore initial 38 ≤ DefaultState.drawsBefore initial (38+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 38 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_38 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_4 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_38] using ob)
#print axioms site_38
#print axioms word_38
#print axioms step_38

theorem site_39 : EntryBinding.plan.code[39]? = some (7204, 2584609065) := rfl
theorem room_39 (initial : NativeState) : 39 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_39 : NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 14#5 = 2584609065#32 := by decide
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
  have member : (7204, 2584609065) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_39
  have pc : x.regs._PC = MemReloc.imageAddress base 7204 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    39 x inv.core (7204, 2584609065) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 14), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 9#5 9#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 9#5 9#5 14#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_39] using ob)
#print axioms site_39
#print axioms word_39
#print axioms step_39

theorem site_40 : EntryBinding.plan.code[40]? = some (7208, 2869887471) := rfl
theorem room_40 (initial : NativeState) : 40 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_40 : NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5 = 2869887471#32 := by decide
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
  have member : (7208, 2869887471) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_40
  have pc : x.regs._PC = MemReloc.imageAddress base 7208 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    40 x inv.core (7208, 2869887471) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_40] using ob)
#print axioms site_40
#print axioms word_40
#print axioms step_40

theorem site_41 : EntryBinding.plan.code[41]? = some (7212, 3121611280) := rfl
theorem room_41 (initial : NativeState) : 41 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_41 : NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5 = 3121611280#32 := by decide
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
  have member : (7212, 3121611280) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_41
  have pc : x.regs._PC = MemReloc.imageAddress base 7212 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    41 x inv.core (7212, 3121611280) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_41] using ob)
#print axioms site_41
#print axioms word_41
#print axioms step_41

theorem site_42 : EntryBinding.plan.code[42]? = some (7216, 2585723177) := rfl
theorem room_42 (initial : NativeState) : 42 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_42 : NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5 = 2585723177#32 := by decide
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
  have member : (7216, 2585723177) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_42
  have pc : x.regs._PC = MemReloc.imageAddress base 7216 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    42 x inv.core (7216, 2585723177) member pc
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
    (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 9#5 9#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_42] using ob)
#print axioms site_42
#print axioms word_42
#print axioms step_42

theorem site_43 : EntryBinding.plan.code[43]? = some (7220, 2869887207) := rfl
theorem room_43 (initial : NativeState) : 43 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_43 : NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 15#5 = 2869887207#32 := by decide
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
  have member : (7220, 2869887207) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_43
  have pc : x.regs._PC = MemReloc.imageAddress base 7220 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    43 x inv.core (7220, 2869887207) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 7#5 7#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_43] using ob)
#print axioms site_43
#print axioms word_43
#print axioms step_43

theorem site_44 : EntryBinding.plan.code[44]? = some (7224, 3121611016) := rfl
theorem room_44 (initial : NativeState) : 44 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_44 : NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5 = 3121611016#32 := by decide
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
  have member : (7224, 3121611016) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_44
  have pc : x.regs._PC = MemReloc.imageAddress base 7224 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    44 x inv.core (7224, 3121611016) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_44] using ob)
#print axioms site_44
#print axioms word_44
#print axioms step_44

theorem site_45 : EntryBinding.plan.code[45]? = some (7228, 2585723177) := rfl
theorem room_45 (initial : NativeState) : 45 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_45 : NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5 = 2585723177#32 := by decide
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
  have member : (7228, 2585723177) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_45
  have pc : x.regs._PC = MemReloc.imageAddress base 7228 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    45 x inv.core (7228, 2585723177) member pc
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
    (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 9#5 9#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_45] using ob)
#print axioms site_45
#print axioms word_45
#print axioms step_45

theorem site_46 : EntryBinding.plan.code[46]? = some (7232, 3943432522) := rfl
theorem room_46 (initial : NativeState) : 46 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_46 : NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 12#5 = 3943432522#32 := by decide
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
  have member : (7232, 3943432522) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_46
  have pc : x.regs._PC = MemReloc.imageAddress base 7232 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    46 x inv.core (7232, 3943432522) member pc
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
    (NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 10#5 10#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 10#5 10#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_46] using ob)
#print axioms site_46
#print axioms word_46
#print axioms step_46

theorem site_47 : EntryBinding.plan.code[47]? = some (7236, 4195156331) := rfl
theorem room_47 (initial : NativeState) : 47 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_47 : NativeEntryBodyDispatch.Sbcs64Reg.selected 11#5 11#5 13#5 = 4195156331#32 := by decide
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
  have member : (7236, 4195156331) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_47
  have pc : x.regs._PC = MemReloc.imageAddress base 7236 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    47 x inv.core (7236, 4195156331) member pc
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
    (NativeEntryBodyDispatch.Sbcs64Reg.selected 11#5 11#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .reg (.x 13), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 11), .reg (.x 13), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64Reg.tailX real x 11#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_0 real x 11#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_47] using ob)
#print axioms site_47
#print axioms word_47
#print axioms step_47

theorem site_48 : EntryBinding.plan.code[48]? = some (7240, 3667862512) := rfl
theorem room_48 (initial : NativeState) : 48 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_48 : NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5 = 3667862512#32 := by decide
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
  have member : (7240, 3667862512) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_48
  have pc : x.regs._PC = MemReloc.imageAddress base 7240 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    48 x inv.core (7240, 3667862512) member pc
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
    (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_2 real x 16#5 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_48] using ob)
#print axioms site_48
#print axioms word_48
#print axioms step_48

theorem site_49 : EntryBinding.plan.code[49]? = some (7244, 3390046538) := rfl
theorem room_49 (initial : NativeState) : 49 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_49 : NativeEntryBodyDispatch.SecpEor64.selected 10#5 10#5 16#5 = 3390046538#32 := by decide
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
  have member : (7244, 3390046538) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_49
  have pc : x.regs._PC = MemReloc.imageAddress base 7244 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    49 x inv.core (7244, 3390046538) member pc
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
    (NativeEntryBodyDispatch.SecpEor64.selected 10#5 10#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.eor, [.reg (.x 10), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_49] using ob)
#print axioms site_49
#print axioms word_49
#print axioms step_49

theorem site_50 : EntryBinding.plan.code[50]? = some (7248, 3943694666) := rfl
theorem room_50 (initial : NativeState) : 50 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_50 : NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 16#5 = 3943694666#32 := by decide
theorem step_50 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 50 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (50+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[50]'(room_50 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7248, 3943694666) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_50
  have pc : x.regs._PC = MemReloc.imageAddress base 7248 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    50 x inv.core (7248, 3943694666) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (50+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 50 + 4#64 = offset EntryBinding.plan (50+1) from by decide)
  have draws : DefaultState.drawsBefore initial 50 ≤ DefaultState.drawsBefore initial (50+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 50 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_50 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 10#5 10#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 10#5 10#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_50] using ob)
#print axioms site_50
#print axioms word_50
#print axioms step_50

theorem site_51 : EntryBinding.plan.code[51]? = some (7252, 3390046571) := rfl
theorem room_51 (initial : NativeState) : 51 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_51 : NativeEntryBodyDispatch.SecpEor64.selected 11#5 11#5 16#5 = 3390046571#32 := by decide
theorem step_51 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 51 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (51+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[51]'(room_51 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7252, 3390046571) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_51
  have pc : x.regs._PC = MemReloc.imageAddress base 7252 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    51 x inv.core (7252, 3390046571) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (51+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 51 + 4#64 = offset EntryBinding.plan (51+1) from by decide)
  have draws : DefaultState.drawsBefore initial 51 ≤ DefaultState.drawsBefore initial (51+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 51 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_51 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpEor64.selected 11#5 11#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.eor, [.reg (.x 11), .reg (.x 16)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpEor64.tailX real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_12 real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_51] using ob)
#print axioms site_51
#print axioms word_51
#print axioms step_51

theorem site_52 : EntryBinding.plan.code[52]? = some (7256, 3658482027) := rfl
theorem room_52 (initial : NativeState) : 52 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_52 : NativeEntryBodyDispatch.SecpSbc64.selected 11#5 11#5 16#5 = 3658482027#32 := by decide
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
  have member : (7256, 3658482027) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_52
  have pc : x.regs._PC = MemReloc.imageAddress base 7256 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    52 x inv.core (7256, 3658482027) member pc
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
    (NativeEntryBodyDispatch.SecpSbc64.selected 11#5 11#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .reg (.x 16), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpSbc64.tailX real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_14 real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_52] using ob)
#print axioms site_52
#print axioms word_52
#print axioms step_52

theorem site_53 : EntryBinding.plan.code[53]? = some (7260, 2869166278) := rfl
theorem room_53 (initial : NativeState) : 53 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_53 : NativeEntryBodyDispatch.AddsShift64.selected 6#5 6#5 0#6 4#5 = 2869166278#32 := by decide
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
  have member : (7260, 2869166278) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_53
  have pc : x.regs._PC = MemReloc.imageAddress base 7260 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    53 x inv.core (7260, 2869166278) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 6#5 6#5 0#6 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 6#5 6#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 6#5 6#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_53] using ob)
#print axioms site_53
#print axioms word_53
#print axioms step_53

theorem site_54 : EntryBinding.plan.code[54]? = some (7264, 3120890087) := rfl
theorem room_54 (initial : NativeState) : 54 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_54 : NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 5#5 = 3120890087#32 := by decide
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
  have member : (7264, 3120890087) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_54
  have pc : x.regs._PC = MemReloc.imageAddress base 7264 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    54 x inv.core (7264, 3120890087) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 7#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 7#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_54] using ob)
#print axioms site_54
#print axioms word_54
#print axioms step_54

theorem site_55 : EntryBinding.plan.code[55]? = some (7268, 3122594056) := rfl
theorem room_55 (initial : NativeState) : 55 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_55 : NativeEntryBodyDispatch.Adcs64ZRm.selected 8#5 8#5 = 3122594056#32 := by decide
theorem step_55 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 55 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (55+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[55]'(room_55 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7268, 3122594056) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_55
  have pc : x.regs._PC = MemReloc.imageAddress base 7268 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    55 x inv.core (7268, 3122594056) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (55+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 55 + 4#64 = offset EntryBinding.plan (55+1) from by decide)
  have draws : DefaultState.drawsBefore initial 55 ≤ DefaultState.drawsBefore initial (55+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 55 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_55 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 8#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 8#5 8#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 8#5 8#5 (by decide) (by decide) (by decide)) next (by simpa only [word_55] using ob)
#print axioms site_55
#print axioms word_55
#print axioms step_55

theorem site_56 : EntryBinding.plan.code[56]? = some (7272, 2585723177) := rfl
theorem room_56 (initial : NativeState) : 56 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_56 : NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5 = 2585723177#32 := by decide
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
  have member : (7272, 2585723177) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_56
  have pc : x.regs._PC = MemReloc.imageAddress base 7272 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    56 x inv.core (7272, 2585723177) member pc
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
    (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 9#5 9#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_56] using ob)
#print axioms site_56
#print axioms word_56
#print axioms step_56

theorem site_57 : EntryBinding.plan.code[57]? = some (7276, 2611641676) := rfl
theorem room_57 (initial : NativeState) : 57 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_57 : N1D226.Umaddl64Generic.Encoding.selected 12#5 10#5 10#5 = 2611641676#32 := by decide
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
  have member : (7276, 2611641676) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_57
  have pc : x.regs._PC = MemReloc.imageAddress base 7276 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    57 x inv.core (7276, 2611641676) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (57+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 57 + 4#64 = offset EntryBinding.plan (57+1) from by decide)
  have draws : DefaultState.drawsBefore initial 57 ≤ DefaultState.drawsBefore initial (57+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 57 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_57 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 12#5 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 12#5 10#5 10#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 12#5 10#5 10#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 12#5 10#5 10#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 12#5 10#5 10#5 vh, memory⟩)
    next (by simpa only [word_57] using ob)
#print axioms site_57
#print axioms word_57
#print axioms step_57

theorem site_58 : EntryBinding.plan.code[58]? = some (7280, 3546348869) := rfl
theorem room_58 (initial : NativeState) : 58 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_58 : NativeEntryBodyDispatch.SecpLsr32.selected 5#5 10#5 = 3546348869#32 := by decide
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
  have member : (7280, 3546348869) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_58
  have pc : x.regs._PC = MemReloc.imageAddress base 7280 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    58 x inv.core (7280, 3546348869) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 5#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 32), [.reg (.x 10)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 5#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 5#5 10#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_58] using ob)
#print axioms site_58
#print axioms word_58
#print axioms step_58

theorem site_59 : EntryBinding.plan.code[59]? = some (7284, 2611313837) := rfl
theorem room_59 (initial : NativeState) : 59 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_59 : N1D226.Umaddl64Generic.Encoding.selected 13#5 5#5 5#5 = 2611313837#32 := by decide
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
  have member : (7284, 2611313837) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_59
  have pc : x.regs._PC = MemReloc.imageAddress base 7284 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    59 x inv.core (7284, 2611313837) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (59+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 59 + 4#64 = offset EntryBinding.plan (59+1) from by decide)
  have draws : DefaultState.drawsBefore initial 59 ≤ DefaultState.drawsBefore initial (59+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 59 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_59 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 13#5 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 13#5 5#5 5#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 13#5 5#5 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 13#5 5#5 5#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 13#5 5#5 5#5 vh, memory⟩)
    next (by simpa only [word_59] using ob)
#print axioms site_59
#print axioms word_59
#print axioms step_59

theorem site_60 : EntryBinding.plan.code[60]? = some (7288, 2611313989) := rfl
theorem room_60 (initial : NativeState) : 60 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_60 : N1D226.Umaddl64Generic.Encoding.selected 5#5 10#5 5#5 = 2611313989#32 := by decide
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
  have member : (7288, 2611313989) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_60
  have pc : x.regs._PC = MemReloc.imageAddress base 7288 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    60 x inv.core (7288, 2611313989) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (60+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 60 + 4#64 = offset EntryBinding.plan (60+1) from by decide)
  have draws : DefaultState.drawsBefore initial 60 ≤ DefaultState.drawsBefore initial (60+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 60 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_60 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 5#5 10#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 10#5 5#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 10#5 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 5#5 10#5 5#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 5#5 10#5 5#5 vh, memory⟩)
    next (by simpa only [word_60] using ob)
#print axioms site_60
#print axioms word_60
#print axioms step_60

theorem site_61 : EntryBinding.plan.code[61]? = some (7292, 2869265804) := rfl
theorem room_61 (initial : NativeState) : 61 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_61 : N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 33#6 5#5 = 2869265804#32 := by decide
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
  have member : (7292, 2869265804) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_61
  have pc : x.regs._PC = MemReloc.imageAddress base 7292 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    61 x inv.core (7292, 2869265804) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (61+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 61 + 4#64 = offset EntryBinding.plan (61+1) from by decide)
  have draws : DefaultState.drawsBefore initial 61 ≤ DefaultState.drawsBefore initial (61+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 61 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_61 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 33#6 5#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 12#5 12#5 33#6 5#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 12#5 33#6 5#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 12#5 12#5 33#6 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 12#5 12#5 33#6 5#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 12#5 12#5 33#6 5#5 vh, memory⟩)
    next (by simpa only [word_61] using ob)
#print axioms site_61
#print axioms word_61
#print axioms step_61

theorem site_62 : EntryBinding.plan.code[62]? = some (7296, 3546283173) := rfl
theorem room_62 (initial : NativeState) : 62 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_62 : NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5 = 3546283173#32 := by decide
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
  have member : (7296, 3546283173) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_62
  have pc : x.regs._PC = MemReloc.imageAddress base 7296 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    62 x inv.core (7296, 3546283173) member pc
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
    (NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 31), [.reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr31.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_4 real x 5#5 5#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_62] using ob)
#print axioms site_62
#print axioms word_62
#print axioms step_62

theorem site_63 : EntryBinding.plan.code[63]? = some (7300, 2584019373) := rfl
theorem room_63 (initial : NativeState) : 63 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_63 : NativeEntryBodyDispatch.Adc64.selected 13#5 13#5 5#5 = 2584019373#32 := by decide
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
  have member : (7300, 2584019373) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_63
  have pc : x.regs._PC = MemReloc.imageAddress base 7300 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    63 x inv.core (7300, 2584019373) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 13#5 13#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 5), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 13#5 13#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 13#5 13#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_63] using ob)
#print axioms site_63
#print axioms word_63
#print axioms step_63

theorem site_64 : EntryBinding.plan.code[64]? = some (7304, 2611707247) := rfl
theorem room_64 (initial : NativeState) : 64 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_64 : N1D226.Umaddl64Generic.Encoding.selected 15#5 11#5 11#5 = 2611707247#32 := by decide
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
  have member : (7304, 2611707247) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_64
  have pc : x.regs._PC = MemReloc.imageAddress base 7304 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    64 x inv.core (7304, 2611707247) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (64+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 64 + 4#64 = offset EntryBinding.plan (64+1) from by decide)
  have draws : DefaultState.drawsBefore initial 64 ≤ DefaultState.drawsBefore initial (64+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 64 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_64 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 15#5 11#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 15#5 11#5 11#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 15#5 11#5 11#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 15#5 11#5 11#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 15#5 11#5 11#5 vh, memory⟩)
    next (by simpa only [word_64] using ob)
#print axioms site_64
#print axioms word_64
#print axioms step_64

theorem site_65 : EntryBinding.plan.code[65]? = some (7308, 3546348901) := rfl
theorem room_65 (initial : NativeState) : 65 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_65 : NativeEntryBodyDispatch.SecpLsr32.selected 5#5 11#5 = 3546348901#32 := by decide
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
  have member : (7308, 3546348901) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_65
  have pc : x.regs._PC = MemReloc.imageAddress base 7308 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    65 x inv.core (7308, 3546348901) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 5#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 32), [.reg (.x 11)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 5#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 5#5 11#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_65] using ob)
#print axioms site_65
#print axioms word_65
#print axioms step_65

theorem site_66 : EntryBinding.plan.code[66]? = some (7312, 2611313838) := rfl
theorem room_66 (initial : NativeState) : 66 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_66 : N1D226.Umaddl64Generic.Encoding.selected 14#5 5#5 5#5 = 2611313838#32 := by decide
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
  have member : (7312, 2611313838) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_66
  have pc : x.regs._PC = MemReloc.imageAddress base 7312 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    66 x inv.core (7312, 2611313838) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (66+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 66 + 4#64 = offset EntryBinding.plan (66+1) from by decide)
  have draws : DefaultState.drawsBefore initial 66 ≤ DefaultState.drawsBefore initial (66+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 66 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_66 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 14#5 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 5#5 5#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 5#5 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 14#5 5#5 5#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 14#5 5#5 5#5 vh, memory⟩)
    next (by simpa only [word_66] using ob)
#print axioms site_66
#print axioms word_66
#print axioms step_66

theorem site_67 : EntryBinding.plan.code[67]? = some (7316, 2611314021) := rfl
theorem room_67 (initial : NativeState) : 67 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_67 : N1D226.Umaddl64Generic.Encoding.selected 5#5 11#5 5#5 = 2611314021#32 := by decide
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
  have member : (7316, 2611314021) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_67
  have pc : x.regs._PC = MemReloc.imageAddress base 7316 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    67 x inv.core (7316, 2611314021) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (67+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 67 + 4#64 = offset EntryBinding.plan (67+1) from by decide)
  have draws : DefaultState.drawsBefore initial 67 ≤ DefaultState.drawsBefore initial (67+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 67 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_67 initial) compiles page (by decide)
    (N1D226.Umaddl64Generic.Encoding.selected 5#5 11#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 11#5 5#5) (none) x inv
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 11#5 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_6 real x 5#5 11#5 5#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.umaddl_outputs x fin 5#5 11#5 5#5 vh, memory⟩)
    next (by simpa only [word_67] using ob)
#print axioms site_67
#print axioms word_67
#print axioms step_67

theorem site_68 : EntryBinding.plan.code[68]? = some (7320, 2601221444) := rfl
theorem room_68 (initial : NativeState) : 68 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_68 : NativeEntryBodyDispatch.Madd64.selected 4#5 10#5 11#5 = 2601221444#32 := by decide
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
  have member : (7320, 2601221444) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_68
  have pc : x.regs._PC = MemReloc.imageAddress base 7320 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    68 x inv.core (7320, 2601221444) member pc
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
    (NativeEntryBodyDispatch.Madd64.selected 4#5 10#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 10), .reg (.x 11)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 4#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 4#5 10#5 11#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_68] using ob)
#print axioms site_68
#print axioms word_68
#print axioms step_68

theorem site_69 : EntryBinding.plan.code[69]? = some (7324, 2613804368) := rfl
theorem room_69 (initial : NativeState) : 69 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_69 : NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5 = 2613804368#32 := by decide
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
  have member : (7324, 2613804368) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_69
  have pc : x.regs._PC = MemReloc.imageAddress base 7324 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    69 x inv.core (7324, 2613804368) member pc
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
    (NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 10), .reg (.x 11)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_69] using ob)
#print axioms site_69
#print axioms word_69
#print axioms step_69

theorem site_70 : EntryBinding.plan.code[70]? = some (7328, 2869265903) := rfl
theorem room_70 (initial : NativeState) : 70 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_70 : N1D226.AddsShift64Generic.Encoding.selected 15#5 15#5 33#6 5#5 = 2869265903#32 := by decide
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
  have member : (7328, 2869265903) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_70
  have pc : x.regs._PC = MemReloc.imageAddress base 7328 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    70 x inv.core (7328, 2869265903) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (70+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 70 + 4#64 = offset EntryBinding.plan (70+1) from by decide)
  have draws : DefaultState.drawsBefore initial 70 ≤ DefaultState.drawsBefore initial (70+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 70 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_70 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 15#5 15#5 33#6 5#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 15#5 15#5 33#6 5#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 15#5 33#6 5#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 15#5 15#5 33#6 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 15#5 15#5 33#6 5#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 15#5 15#5 33#6 5#5 vh, memory⟩)
    next (by simpa only [word_70] using ob)
#print axioms site_70
#print axioms word_70
#print axioms step_70

theorem site_71 : EntryBinding.plan.code[71]? = some (7332, 3546283173) := rfl
theorem room_71 (initial : NativeState) : 71 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_71 : NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5 = 3546283173#32 := by decide
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
  have member : (7332, 3546283173) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_71
  have pc : x.regs._PC = MemReloc.imageAddress base 7332 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    71 x inv.core (7332, 3546283173) member pc
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
    (NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 31), [.reg (.x 5)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr31.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_4 real x 5#5 5#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_71] using ob)
#print axioms site_71
#print axioms word_71
#print axioms step_71

theorem site_72 : EntryBinding.plan.code[72]? = some (7336, 2584019406) := rfl
theorem room_72 (initial : NativeState) : 72 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_72 : NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 5#5 = 2584019406#32 := by decide
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
  have member : (7336, 2584019406) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_72
  have pc : x.regs._PC = MemReloc.imageAddress base 7336 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    72 x inv.core (7336, 2584019406) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 5), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 14#5 14#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_72] using ob)
#print axioms site_72
#print axioms word_72
#print axioms step_72

theorem site_73 : EntryBinding.plan.code[73]? = some (7340, 2869166212) := rfl
theorem room_73 (initial : NativeState) : 73 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_73 : NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 4#5 = 2869166212#32 := by decide
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
  have member : (7340, 2869166212) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_73
  have pc : x.regs._PC = MemReloc.imageAddress base 7340 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    73 x inv.core (7340, 2869166212) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 4#5 4#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 4#5 4#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_73] using ob)
#print axioms site_73
#print axioms word_73
#print axioms step_73

theorem site_74 : EntryBinding.plan.code[74]? = some (7344, 3121611280) := rfl
theorem room_74 (initial : NativeState) : 74 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_74 : NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5 = 3121611280#32 := by decide
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
  have member : (7344, 3121611280) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_74
  have pc : x.regs._PC = MemReloc.imageAddress base 7344 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    74 x inv.core (7344, 3121611280) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_74] using ob)
#print axioms site_74
#print axioms word_74
#print axioms step_74

theorem site_75 : EntryBinding.plan.code[75]? = some (7348, 2585723342) := rfl
theorem room_75 (initial : NativeState) : 75 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_75 : NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5 = 2585723342#32 := by decide
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
  have member : (7348, 2585723342) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_75
  have pc : x.regs._PC = MemReloc.imageAddress base 7348 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    75 x inv.core (7348, 2585723342) member pc
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
    (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_75] using ob)
#print axioms site_75
#print axioms word_75
#print axioms step_75

theorem site_76 : EntryBinding.plan.code[76]? = some (7352, 2869166509) := rfl
theorem room_76 (initial : NativeState) : 76 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_76 : NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 4#5 = 2869166509#32 := by decide
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
  have member : (7352, 2869166509) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_76
  have pc : x.regs._PC = MemReloc.imageAddress base 7352 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    76 x inv.core (7352, 2869166509) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 13#5 13#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_76] using ob)
#print axioms site_76
#print axioms word_76
#print axioms step_76

theorem site_77 : EntryBinding.plan.code[77]? = some (7356, 3121611247) := rfl
theorem room_77 (initial : NativeState) : 77 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_77 : NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 16#5 = 3121611247#32 := by decide
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
  have member : (7356, 3121611247) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_77
  have pc : x.regs._PC = MemReloc.imageAddress base 7356 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    77 x inv.core (7356, 3121611247) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (77+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 77 + 4#64 = offset EntryBinding.plan (77+1) from by decide)
  have draws : DefaultState.drawsBefore initial 77 ≤ DefaultState.drawsBefore initial (77+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 77 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_77 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_77] using ob)
#print axioms site_77
#print axioms word_77
#print axioms step_77

theorem site_78 : EntryBinding.plan.code[78]? = some (7360, 2585723342) := rfl
theorem room_78 (initial : NativeState) : 78 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_78 : NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5 = 2585723342#32 := by decide
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
  have member : (7360, 2585723342) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_78
  have pc : x.regs._PC = MemReloc.imageAddress base 7360 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    78 x inv.core (7360, 2585723342) member pc
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
    (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_6 real x 14#5 14#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_78] using ob)
#print axioms site_78
#print axioms word_78
#print axioms step_78

theorem site_79 : EntryBinding.plan.code[79]? = some (7364, 2869297220) := rfl
theorem room_79 (initial : NativeState) : 79 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_79 : NativeEntryBodyDispatch.AddsShift64.selected 4#5 2#5 0#6 6#5 = 2869297220#32 := by decide
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
  have member : (7364, 2869297220) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_79
  have pc : x.regs._PC = MemReloc.imageAddress base 7364 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    79 x inv.core (7364, 2869297220) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 4#5 2#5 0#6 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 4#5 2#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 4#5 2#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_79] using ob)
#print axioms site_79
#print axioms word_79
#print axioms step_79

theorem site_80 : EntryBinding.plan.code[80]? = some (7368, 3121021029) := rfl
theorem room_80 (initial : NativeState) : 80 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_80 : NativeEntryBodyDispatch.Adcs64.selected 5#5 3#5 7#5 = 3121021029#32 := by decide
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
  have member : (7368, 3121021029) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_80
  have pc : x.regs._PC = MemReloc.imageAddress base 7368 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    80 x inv.core (7368, 3121021029) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 5#5 3#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 5#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 5#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_80] using ob)
#print axioms site_80
#print axioms word_80
#print axioms step_80

theorem site_81 : EntryBinding.plan.code[81]? = some (7372, 3121086662) := rfl
theorem room_81 (initial : NativeState) : 81 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_81 : NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 8#5 = 3121086662#32 := by decide
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
  have member : (7372, 3121086662) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_81
  have pc : x.regs._PC = MemReloc.imageAddress base 7372 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    81 x inv.core (7372, 3121086662) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 6#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 6#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_81] using ob)
#print axioms site_81
#print axioms word_81
#print axioms step_81

theorem site_82 : EntryBinding.plan.code[82]? = some (7376, 3121152231) := rfl
theorem room_82 (initial : NativeState) : 82 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_82 : NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 9#5 = 3121152231#32 := by decide
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
  have member : (7376, 3121152231) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_82
  have pc : x.regs._PC = MemReloc.imageAddress base 7376 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    82 x inv.core (7376, 3121152231) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (82+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 82 + 4#64 = offset EntryBinding.plan (82+1) from by decide)
  have draws : DefaultState.drawsBefore initial 82 ≤ DefaultState.drawsBefore initial (82+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 82 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_82 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 7#5 7#5 9#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 7#5 7#5 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_82] using ob)
#print axioms site_82
#print axioms word_82
#print axioms step_82

theorem site_83 : EntryBinding.plan.code[83]? = some (7380, 3667862512) := rfl
theorem room_83 (initial : NativeState) : 83 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_83 : NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5 = 3667862512#32 := by decide
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
  have member : (7380, 3667862512) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_83
  have pc : x.regs._PC = MemReloc.imageAddress base 7380 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    83 x inv.core (7380, 3667862512) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (83+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 83 + 4#64 = offset EntryBinding.plan (83+1) from by decide)
  have draws : DefaultState.drawsBefore initial 83 ≤ DefaultState.drawsBefore initial (83+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 83 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_83 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_2 real x 16#5 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_83] using ob)
#print axioms site_83
#print axioms word_83
#print axioms step_83

theorem site_84 : EntryBinding.plan.code[84]? = some (7384, 3943432324) := rfl
theorem room_84 (initial : NativeState) : 84 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_84 : NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 12#5 = 3943432324#32 := by decide
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
  have member : (7384, 3943432324) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_84
  have pc : x.regs._PC = MemReloc.imageAddress base 7384 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    84 x inv.core (7384, 3943432324) member pc
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
    (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 4#5 4#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_84] using ob)
#print axioms site_84
#print axioms word_84
#print axioms step_84

theorem site_85 : EntryBinding.plan.code[85]? = some (7388, 4195156133) := rfl
theorem room_85 (initial : NativeState) : 85 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_85 : NativeEntryBodyDispatch.Sbcs64Reg.selected 5#5 5#5 13#5 = 4195156133#32 := by decide
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
  have member : (7388, 4195156133) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_85
  have pc : x.regs._PC = MemReloc.imageAddress base 7388 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    85 x inv.core (7388, 4195156133) member pc
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
    (NativeEntryBodyDispatch.Sbcs64Reg.selected 5#5 5#5 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .reg (.x 13), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 13), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64Reg.tailX real x 5#5 5#5 13#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_0 real x 5#5 5#5 13#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_85] using ob)
#print axioms site_85
#print axioms word_85
#print axioms step_85

theorem site_86 : EntryBinding.plan.code[86]? = some (7392, 4195287238) := rfl
theorem room_86 (initial : NativeState) : 86 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_86 : NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 6#5 15#5 = 4195287238#32 := by decide
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
  have member : (7392, 4195287238) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_86
  have pc : x.regs._PC = MemReloc.imageAddress base 7392 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    86 x inv.core (7392, 4195287238) member pc
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
    (NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 6#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64Reg.tailX real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_0 real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_86] using ob)
#print axioms site_86
#print axioms word_86
#print axioms step_86

theorem site_87 : EntryBinding.plan.code[87]? = some (7396, 4195221735) := rfl
theorem room_87 (initial : NativeState) : 87 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_87 : NativeEntryBodyDispatch.Sbcs64Reg.selected 7#5 7#5 14#5 = 4195221735#32 := by decide
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
  have member : (7396, 4195221735) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_87
  have pc : x.regs._PC = MemReloc.imageAddress base 7396 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    87 x inv.core (7396, 4195221735) member pc
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
    (NativeEntryBodyDispatch.Sbcs64Reg.selected 7#5 7#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.sbc3, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64Reg.tailX real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_0 real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_87] using ob)
#print axioms site_87
#print axioms word_87
#print axioms step_87

theorem site_88 : EntryBinding.plan.code[88]? = some (7400, 3121611016) := rfl
theorem room_88 (initial : NativeState) : 88 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_88 : NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5 = 3121611016#32 := by decide
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
  have member : (7400, 3121611016) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_88
  have pc : x.regs._PC = MemReloc.imageAddress base 7400 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    88 x inv.core (7400, 3121611016) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_88] using ob)
#print axioms site_88
#print axioms word_88
#print axioms step_88

theorem site_89 : EntryBinding.plan.code[89]? = some (7404, 2584740137) := rfl
theorem room_89 (initial : NativeState) : 89 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_89 : NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 16#5 = 2584740137#32 := by decide
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
  have member : (7404, 2584740137) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_89
  have pc : x.regs._PC = MemReloc.imageAddress base 7404 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    89 x inv.core (7404, 2584740137) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 16), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 9#5 9#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 9#5 9#5 16#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_89] using ob)
#print axioms site_89
#print axioms word_89
#print axioms step_89

theorem site_90 : EntryBinding.plan.code[90]? = some (7408, 3531635249) := rfl
theorem room_90 (initial : NativeState) : 90 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_90 : NativeEntryBodyDispatch.Movz64z.selected 17#5 977#16 = 3531635249#32 := by decide
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
  have member : (7408, 3531635249) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_90
  have pc : x.regs._PC = MemReloc.imageAddress base 7408 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    90 x inv.core (7408, 3531635249) member pc
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
    (NativeEntryBodyDispatch.Movz64z.selected 17#5 977#16) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 17), some ⟨(.const 977#64), []⟩)] (none) (by rfl) x inv
    (ArmCertValue.Movz64z.tailX real x 17#5 977#16 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_2 real x 17#5 977#16 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_90] using ob)
#print axioms site_90
#print axioms word_90
#print axioms step_90

theorem site_91 : EntryBinding.plan.code[91]? = some (7412, 2992636464) := rfl
theorem room_91 (initial : NativeState) : 91 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_91 : NativeEntryBodyDispatch.OrrImm32_0.selected 16#5 17#5 = 2992636464#32 := by decide
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
  have member : (7412, 2992636464) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_91
  have pc : x.regs._PC = MemReloc.imageAddress base 7412 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    91 x inv.core (7412, 2992636464) member pc
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
    (NativeEntryBodyDispatch.OrrImm32_0.selected 16#5 17#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨.orr, [.reg (.x 17), .lit 4294967296#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.OrrImm32_0.tailX real x 16#5 17#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_8 real x 16#5 17#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_91] using ob)
#print axioms site_91
#print axioms word_91
#print axioms step_91

theorem site_92 : EntryBinding.plan.code[92]? = some (7416, 2600893962) := rfl
theorem room_92 (initial : NativeState) : 92 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_92 : NativeEntryBodyDispatch.Madd64.selected 10#5 16#5 6#5 = 2600893962#32 := by decide
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
  have member : (7416, 2600893962) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_92
  have pc : x.regs._PC = MemReloc.imageAddress base 7416 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    92 x inv.core (7416, 2600893962) member pc
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
    (NativeEntryBodyDispatch.Madd64.selected 10#5 16#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.mul, [.reg (.x 16), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 10#5 16#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 10#5 16#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_92] using ob)
#print axioms site_92
#print axioms word_92
#print axioms step_92

theorem site_93 : EntryBinding.plan.code[93]? = some (7420, 2613476877) := rfl
theorem room_93 (initial : NativeState) : 93 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_93 : NativeEntryBodyDispatch.Umulh64.selected 13#5 16#5 6#5 = 2613476877#32 := by decide
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
  have member : (7420, 2613476877) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_93
  have pc : x.regs._PC = MemReloc.imageAddress base 7420 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    93 x inv.core (7420, 2613476877) member pc
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
    (NativeEntryBodyDispatch.Umulh64.selected 13#5 16#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 16), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 13#5 16#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 13#5 16#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_93] using ob)
#print axioms site_93
#print axioms word_93
#print axioms step_93

theorem site_94 : EntryBinding.plan.code[94]? = some (7424, 2453699814) := rfl
theorem room_94 (initial : NativeState) : 94 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_94 : NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 7#5 = 2453699814#32 := by decide
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
  have member : (7424, 2453699814) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_94
  have pc : x.regs._PC = MemReloc.imageAddress base 7424 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    94 x inv.core (7424, 2453699814) member pc
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
    (NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 7), .lit 4294967295#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpAndMask32.tailX real x 6#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_0 real x 6#5 7#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_94] using ob)
#print axioms site_94
#print axioms word_94
#print axioms step_94

theorem site_95 : EntryBinding.plan.code[95]? = some (7428, 3546348775) := rfl
theorem room_95 (initial : NativeState) : 95 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_95 : NativeEntryBodyDispatch.SecpLsr32.selected 7#5 7#5 = 3546348775#32 := by decide
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
  have member : (7428, 3546348775) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_95
  have pc : x.regs._PC = MemReloc.imageAddress base 7428 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    95 x inv.core (7428, 3546348775) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 7#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨(.lsr 32), [.reg (.x 7)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 7#5 7#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_95] using ob)
#print axioms site_95
#print axioms word_95
#print axioms step_95

theorem site_96 : EntryBinding.plan.code[96]? = some (7432, 2600893995) := rfl
theorem room_96 (initial : NativeState) : 96 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_96 : NativeEntryBodyDispatch.Madd64.selected 11#5 17#5 6#5 = 2600893995#32 := by decide
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
  have member : (7432, 2600893995) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_96
  have pc : x.regs._PC = MemReloc.imageAddress base 7432 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    96 x inv.core (7432, 2600893995) member pc
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
    (NativeEntryBodyDispatch.Madd64.selected 11#5 17#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 11#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 11#5 17#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_96] using ob)
#print axioms site_96
#print axioms word_96
#print axioms step_96

theorem site_97 : EntryBinding.plan.code[97]? = some (7436, 2600933926) := rfl
theorem room_97 (initial : NativeState) : 97 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_97 : N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5 = 2600933926#32 := by decide
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
  have member : (7436, 2600933926) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_97
  have pc : x.regs._PC = MemReloc.imageAddress base 7436 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    97 x inv.core (7436, 2600933926) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (97+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 97 + 4#64 = offset EntryBinding.plan (97+1) from by decide)
  have draws : DefaultState.drawsBefore initial 97 ≤ DefaultState.drawsBefore initial (97+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 97 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_97 initial) compiles page (by decide)
    (N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 6#5 17#5 6#5 7#5) (none) x inv
    (N1D226.Madd64Generic.DriverValue.tailX real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_5 real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.madd_outputs x fin 6#5 17#5 6#5 7#5 vh, memory⟩)
    next (by simpa only [word_97] using ob)
#print axioms site_97
#print axioms word_97
#print axioms step_97

theorem site_98 : EntryBinding.plan.code[98]? = some (7440, 2869330283) := rfl
theorem room_98 (initial : NativeState) : 98 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_98 : N1D226.AddsShift64Generic.Encoding.selected 11#5 11#5 32#6 6#5 = 2869330283#32 := by decide
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
  have member : (7440, 2869330283) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_98
  have pc : x.regs._PC = MemReloc.imageAddress base 7440 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    98 x inv.core (7440, 2869330283) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (98+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 98 + 4#64 = offset EntryBinding.plan (98+1) from by decide)
  have draws : DefaultState.drawsBefore initial 98 ≤ DefaultState.drawsBefore initial (98+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 98 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_98 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 11#5 11#5 32#6 6#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 11#5 11#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 11#5 32#6 6#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 11#5 11#5 32#6 6#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 11#5 11#5 32#6 6#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 11#5 11#5 32#6 6#5 vh, memory⟩)
    next (by simpa only [word_98] using ob)
#print axioms site_98
#print axioms word_98
#print axioms step_98

theorem site_99 : EntryBinding.plan.code[99]? = some (7444, 3546348742) := rfl
theorem room_99 (initial : NativeState) : 99 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_99 : NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5 = 3546348742#32 := by decide
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
  have member : (7444, 3546348742) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_99
  have pc : x.regs._PC = MemReloc.imageAddress base 7444 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    99 x inv.core (7444, 3546348742) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 6#5 6#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_99] using ob)
#print axioms site_99
#print axioms word_99
#print axioms step_99

theorem site_100 : EntryBinding.plan.code[100]? = some (7448, 2584084718) := rfl
theorem room_100 (initial : NativeState) : 100 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_100 : NativeEntryBodyDispatch.Adc64.selected 14#5 7#5 6#5 = 2584084718#32 := by decide
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
  have member : (7448, 2584084718) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_100
  have pc : x.regs._PC = MemReloc.imageAddress base 7448 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    100 x inv.core (7448, 2584084718) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 14#5 7#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 7), .reg (.x 6), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 14#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 14#5 7#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_100] using ob)
#print axioms site_100
#print axioms word_100
#print axioms step_100

theorem site_101 : EntryBinding.plan.code[101]? = some (7452, 2601025036) := rfl
theorem room_101 (initial : NativeState) : 101 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_101 : NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 8#5 = 2601025036#32 := by decide
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
  have member : (7452, 2601025036) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_101
  have pc : x.regs._PC = MemReloc.imageAddress base 7452 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    101 x inv.core (7452, 2601025036) member pc
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
    (NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 16), .reg (.x 8)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 12#5 16#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 12#5 16#5 8#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_101] using ob)
#print axioms site_101
#print axioms word_101
#print axioms step_101

theorem site_102 : EntryBinding.plan.code[102]? = some (7456, 2613607944) := rfl
theorem room_102 (initial : NativeState) : 102 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_102 : NativeEntryBodyDispatch.Umulh64.selected 8#5 16#5 8#5 = 2613607944#32 := by decide
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
  have member : (7456, 2613607944) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_102
  have pc : x.regs._PC = MemReloc.imageAddress base 7456 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    102 x inv.core (7456, 2613607944) member pc
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
    (NativeEntryBodyDispatch.Umulh64.selected 8#5 16#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 16), .reg (.x 8)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 8#5 16#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 8#5 16#5 8#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_102] using ob)
#print axioms site_102
#print axioms word_102
#print axioms step_102

theorem site_103 : EntryBinding.plan.code[103]? = some (7460, 2453699878) := rfl
theorem room_103 (initial : NativeState) : 103 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_103 : NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 9#5 = 2453699878#32 := by decide
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
  have member : (7460, 2453699878) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_103
  have pc : x.regs._PC = MemReloc.imageAddress base 7460 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    103 x inv.core (7460, 2453699878) member pc
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
    (NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 9), .lit 4294967295#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpAndMask32.tailX real x 6#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_0 real x 6#5 9#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_103] using ob)
#print axioms site_103
#print axioms word_103
#print axioms step_103

theorem site_104 : EntryBinding.plan.code[104]? = some (7464, 3546348839) := rfl
theorem room_104 (initial : NativeState) : 104 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_104 : NativeEntryBodyDispatch.SecpLsr32.selected 7#5 9#5 = 3546348839#32 := by decide
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
  have member : (7464, 3546348839) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_104
  have pc : x.regs._PC = MemReloc.imageAddress base 7464 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    104 x inv.core (7464, 3546348839) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 7#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨(.lsr 32), [.reg (.x 9)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 7#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 7#5 9#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_104] using ob)
#print axioms site_104
#print axioms word_104
#print axioms step_104

theorem site_105 : EntryBinding.plan.code[105]? = some (7468, 2600893993) := rfl
theorem room_105 (initial : NativeState) : 105 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_105 : NativeEntryBodyDispatch.Madd64.selected 9#5 17#5 6#5 = 2600893993#32 := by decide
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
  have member : (7468, 2600893993) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_105
  have pc : x.regs._PC = MemReloc.imageAddress base 7468 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    105 x inv.core (7468, 2600893993) member pc
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
    (NativeEntryBodyDispatch.Madd64.selected 9#5 17#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 9#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 9#5 17#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_105] using ob)
#print axioms site_105
#print axioms word_105
#print axioms step_105

theorem site_106 : EntryBinding.plan.code[106]? = some (7472, 2600933926) := rfl
theorem room_106 (initial : NativeState) : 106 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_106 : N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5 = 2600933926#32 := by decide
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
  have member : (7472, 2600933926) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_106
  have pc : x.regs._PC = MemReloc.imageAddress base 7472 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    106 x inv.core (7472, 2600933926) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (106+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 106 + 4#64 = offset EntryBinding.plan (106+1) from by decide)
  have draws : DefaultState.drawsBefore initial 106 ≤ DefaultState.drawsBefore initial (106+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 106 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_106 initial) compiles page (by decide)
    (N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 6#5 17#5 6#5 7#5) (none) x inv
    (N1D226.Madd64Generic.DriverValue.tailX real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_5 real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.madd_outputs x fin 6#5 17#5 6#5 7#5 vh, memory⟩)
    next (by simpa only [word_106] using ob)
#print axioms site_106
#print axioms word_106
#print axioms step_106

theorem site_107 : EntryBinding.plan.code[107]? = some (7476, 2869330217) := rfl
theorem room_107 (initial : NativeState) : 107 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_107 : N1D226.AddsShift64Generic.Encoding.selected 9#5 9#5 32#6 6#5 = 2869330217#32 := by decide
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
  have member : (7476, 2869330217) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_107
  have pc : x.regs._PC = MemReloc.imageAddress base 7476 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    107 x inv.core (7476, 2869330217) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (107+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 107 + 4#64 = offset EntryBinding.plan (107+1) from by decide)
  have draws : DefaultState.drawsBefore initial 107 ≤ DefaultState.drawsBefore initial (107+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 107 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_107 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 9#5 9#5 32#6 6#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 9#5 9#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 9#5 32#6 6#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 9#5 9#5 32#6 6#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 9#5 9#5 32#6 6#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 9#5 9#5 32#6 6#5 vh, memory⟩)
    next (by simpa only [word_107] using ob)
#print axioms site_107
#print axioms word_107
#print axioms step_107

theorem site_108 : EntryBinding.plan.code[108]? = some (7480, 3546348742) := rfl
theorem room_108 (initial : NativeState) : 108 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_108 : NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5 = 3546348742#32 := by decide
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
  have member : (7480, 3546348742) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_108
  have pc : x.regs._PC = MemReloc.imageAddress base 7480 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    108 x inv.core (7480, 3546348742) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 6#5 6#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_108] using ob)
#print axioms site_108
#print axioms word_108
#print axioms step_108

theorem site_109 : EntryBinding.plan.code[109]? = some (7484, 2584084719) := rfl
theorem room_109 (initial : NativeState) : 109 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_109 : NativeEntryBodyDispatch.Adc64.selected 15#5 7#5 6#5 = 2584084719#32 := by decide
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
  have member : (7484, 2584084719) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_109
  have pc : x.regs._PC = MemReloc.imageAddress base 7484 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    109 x inv.core (7484, 2584084719) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 15#5 7#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 7), .reg (.x 6), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 15#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 15#5 7#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_109] using ob)
#print axioms site_109
#print axioms word_109
#print axioms step_109

theorem site_110 : EntryBinding.plan.code[110]? = some (7488, 2869559362) := rfl
theorem room_110 (initial : NativeState) : 110 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_110 : NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5 = 2869559362#32 := by decide
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
  have member : (7488, 2869559362) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_110
  have pc : x.regs._PC = MemReloc.imageAddress base 7488 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    110 x inv.core (7488, 2869559362) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨.add3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_110] using ob)
#print axioms site_110
#print axioms word_110
#print axioms step_110

theorem site_111 : EntryBinding.plan.code[111]? = some (7492, 3121283171) := rfl
theorem room_111 (initial : NativeState) : 111 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_111 : NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5 = 3121283171#32 := by decide
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
  have member : (7492, 3121283171) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_111
  have pc : x.regs._PC = MemReloc.imageAddress base 7492 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    111 x inv.core (7492, 3121283171) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_111] using ob)
#print axioms site_111
#print axioms word_111
#print axioms step_111

theorem site_112 : EntryBinding.plan.code[112]? = some (7496, 3121348740) := rfl
theorem room_112 (initial : NativeState) : 112 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_112 : NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 12#5 = 3121348740#32 := by decide
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
  have member : (7496, 3121348740) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_112
  have pc : x.regs._PC = MemReloc.imageAddress base 7496 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    112 x inv.core (7496, 3121348740) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 12#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 12#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 4#5 4#5 12#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_112] using ob)
#print axioms site_112
#print axioms word_112
#print axioms step_112

theorem site_113 : EntryBinding.plan.code[113]? = some (7500, 3121152165) := rfl
theorem room_113 (initial : NativeState) : 113 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_113 : NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 9#5 = 3121152165#32 := by decide
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
  have member : (7500, 3121152165) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_113
  have pc : x.regs._PC = MemReloc.imageAddress base 7500 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    113 x inv.core (7500, 3121152165) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_113] using ob)
#print axioms site_113
#print axioms word_113
#print axioms step_113

theorem site_114 : EntryBinding.plan.code[114]? = some (7504, 2594125798) := rfl
theorem room_114 (initial : NativeState) : 114 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_114 : NativeEntryBodyDispatch.Csinc3.selected 6#5 = 2594125798#32 := by decide
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
  have member : (7504, 2594125798) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_114
  have pc : x.regs._PC = MemReloc.imageAddress base 7504 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    114 x inv.core (7504, 2594125798) member pc
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
    (NativeEntryBodyDispatch.Csinc3.selected 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Csinc3.tailX real x 6#5 (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_17 real x 6#5 (by decide) (by decide)) next (by simpa only [word_114] using ob)
#print axioms site_114
#print axioms word_114
#print axioms step_114

theorem site_115 : EntryBinding.plan.code[115]? = some (7508, 2869756003) := rfl
theorem room_115 (initial : NativeState) : 115 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_115 : NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 13#5 = 2869756003#32 := by decide
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
  have member : (7508, 2869756003) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_115
  have pc : x.regs._PC = MemReloc.imageAddress base 7508 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    115 x inv.core (7508, 2869756003) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 13#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 3#5 3#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_115] using ob)
#print axioms site_115
#print axioms word_115
#print axioms step_115

theorem site_116 : EntryBinding.plan.code[116]? = some (7512, 3121479812) := rfl
theorem room_116 (initial : NativeState) : 116 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_116 : NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 14#5 = 3121479812#32 := by decide
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
  have member : (7512, 3121479812) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_116
  have pc : x.regs._PC = MemReloc.imageAddress base 7512 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    116 x inv.core (7512, 3121479812) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 14#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 14#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 4#5 4#5 14#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_116] using ob)
#print axioms site_116
#print axioms word_116
#print axioms step_116

theorem site_117 : EntryBinding.plan.code[117]? = some (7516, 3121086629) := rfl
theorem room_117 (initial : NativeState) : 117 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_117 : NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5 = 3121086629#32 := by decide
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
  have member : (7516, 3121086629) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_117
  have pc : x.regs._PC = MemReloc.imageAddress base 7516 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    117 x inv.core (7516, 3121086629) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_117] using ob)
#print axioms site_117
#print axioms word_117
#print axioms step_117

theorem site_118 : EntryBinding.plan.code[118]? = some (7520, 2584674502) := rfl
theorem room_118 (initial : NativeState) : 118 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_118 : NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 15#5 = 2584674502#32 := by decide
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
  have member : (7520, 2584674502) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_118
  have pc : x.regs._PC = MemReloc.imageAddress base 7520 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    118 x inv.core (7520, 2584674502) member pc
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
    (NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 15#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Adc64.tailX real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_5 real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_118] using ob)
#print axioms site_118
#print axioms word_118
#print axioms step_118

theorem site_119 : EntryBinding.plan.code[119]? = some (7524, 2432697542) := rfl
theorem room_119 (initial : NativeState) : 119 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_119 : NativeEntryBodyDispatch.AddImm64.selected 6#5 6#5 1#12 = 2432697542#32 := by decide
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
  have member : (7524, 2432697542) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_119
  have pc : x.regs._PC = MemReloc.imageAddress base 7524 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    119 x inv.core (7524, 2432697542) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (119+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 119 + 4#64 = offset EntryBinding.plan (119+1) from by decide)
  have draws : DefaultState.drawsBefore initial 119 ≤ DefaultState.drawsBefore initial (119+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 119 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_119 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddImm64.selected 6#5 6#5 1#12) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add, [.reg (.x 6), .lit 1#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.AddImm64.tailX real x 6#5 6#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) (TranslateScalarTagCheck.Tails.tail_1 real x 6#5 6#5 1#12 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_119] using ob)
#print axioms site_119
#print axioms word_119
#print axioms step_119

theorem site_120 : EntryBinding.plan.code[120]? = some (7528, 2600893994) := rfl
theorem room_120 (initial : NativeState) : 120 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_120 : NativeEntryBodyDispatch.Madd64.selected 10#5 17#5 6#5 = 2600893994#32 := by decide
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
  have member : (7528, 2600893994) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_120
  have pc : x.regs._PC = MemReloc.imageAddress base 7528 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    120 x inv.core (7528, 2600893994) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (120+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 120 + 4#64 = offset EntryBinding.plan (120+1) from by decide)
  have draws : DefaultState.drawsBefore initial 120 ≤ DefaultState.drawsBefore initial (120+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 120 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_120 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 10#5 17#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 10#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 10#5 17#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_120] using ob)
#print axioms site_120
#print axioms word_120
#print axioms step_120

theorem site_121 : EntryBinding.plan.code[121]? = some (7532, 3546348747) := rfl
theorem room_121 (initial : NativeState) : 121 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_121 : NativeEntryBodyDispatch.SecpLsr32.selected 11#5 6#5 = 3546348747#32 := by decide
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
  have member : (7532, 3546348747) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_121
  have pc : x.regs._PC = MemReloc.imageAddress base 7532 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    121 x inv.core (7532, 3546348747) member pc
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
    (NativeEntryBodyDispatch.SecpLsr32.selected 11#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpLsr32.tailX real x 11#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_5 real x 11#5 6#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_121] using ob)
#print axioms site_121
#print axioms word_121
#print axioms step_121

theorem site_122 : EntryBinding.plan.code[122]? = some (7536, 2869330250) := rfl
theorem room_122 (initial : NativeState) : 122 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_122 : N1D226.AddsShift64Generic.Encoding.selected 10#5 10#5 32#6 6#5 = 2869330250#32 := by decide
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
  have member : (7536, 2869330250) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_122
  have pc : x.regs._PC = MemReloc.imageAddress base 7536 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    122 x inv.core (7536, 2869330250) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (122+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 122 + 4#64 = offset EntryBinding.plan (122+1) from by decide)
  have draws : DefaultState.drawsBefore initial 122 ≤ DefaultState.drawsBefore initial (122+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 122 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_122 initial) compiles page (by decide)
    (N1D226.AddsShift64Generic.Encoding.selected 10#5 10#5 32#6 6#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 10#5 10#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 10#5 32#6 6#5)) x inv
    (N1D226.AddsShift64Generic.Value.tailX real x 10#5 10#5 32#6 6#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_8 real x 10#5 10#5 32#6 6#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact ⟨TranslateSpan.NativeExprCuts.adds_outputs x fin 10#5 10#5 32#6 6#5 vh, memory⟩)
    next (by simpa only [word_122] using ob)
#print axioms site_122
#print axioms word_122
#print axioms step_122

theorem site_123 : EntryBinding.plan.code[123]? = some (7540, 2584413163) := rfl
theorem room_123 (initial : NativeState) : 123 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_123 : N1D226.AdcZeroRn64Generic.Encoding.selected 11#5 11#5 = 2584413163#32 := by decide
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
  have member : (7540, 2584413163) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_123
  have pc : x.regs._PC = MemReloc.imageAddress base 7540 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    123 x inv.core (7540, 2584413163) member pc
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
    (N1D226.AdcZeroRn64Generic.Encoding.selected 11#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.lit 0#64, .reg (.x 11), .flag 2]⟩)] (none) (by rfl) x inv
    (N1D226.AdcZeroRn64Generic.Value.tailX real x 11#5 11#5 (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_13 real x 11#5 11#5 (by decide) (by decide)) next (by simpa only [word_123] using ob)
#print axioms site_123
#print axioms word_123
#print axioms step_123

theorem site_124 : EntryBinding.plan.code[124]? = some (7544, 2869559362) := rfl
theorem room_124 (initial : NativeState) : 124 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_124 : NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5 = 2869559362#32 := by decide
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
  have member : (7544, 2869559362) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_124
  have pc : x.regs._PC = MemReloc.imageAddress base 7544 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    124 x inv.core (7544, 2869559362) member pc
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
    (NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨.add3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_124] using ob)
#print axioms site_124
#print axioms word_124
#print axioms step_124

theorem site_125 : EntryBinding.plan.code[125]? = some (7548, 3121283171) := rfl
theorem room_125 (initial : NativeState) : 125 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_125 : NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5 = 3121283171#32 := by decide
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
  have member : (7548, 3121283171) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_125
  have pc : x.regs._PC = MemReloc.imageAddress base 7548 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    125 x inv.core (7548, 3121283171) member pc
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
    (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_125] using ob)
#print axioms site_125
#print axioms word_125
#print axioms step_125

theorem site_126 : EntryBinding.plan.code[126]? = some (7552, 3122593924) := rfl
theorem room_126 (initial : NativeState) : 126 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_126 : NativeEntryBodyDispatch.Adcs64ZRm.selected 4#5 4#5 = 3122593924#32 := by decide
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
  have member : (7552, 3122593924) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_126
  have pc : x.regs._PC = MemReloc.imageAddress base 7552 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    126 x inv.core (7552, 3122593924) member pc
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
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 4#5 4#5 (by decide) (by decide) (by decide)) next (by simpa only [word_126] using ob)
#print axioms site_126
#print axioms word_126
#print axioms step_126

theorem site_127 : EntryBinding.plan.code[127]? = some (7556, 3122593957) := rfl
theorem room_127 (initial : NativeState) : 127 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_127 : NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5 = 3122593957#32 := by decide
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
  have member : (7556, 3122593957) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_127
  have pc : x.regs._PC = MemReloc.imageAddress base 7556 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    127 x inv.core (7556, 3122593957) member pc
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
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 5#5 5#5 (by decide) (by decide) (by decide)) next (by simpa only [word_127] using ob)
#print axioms site_127
#print axioms word_127
#print axioms step_127

theorem site_128 : EntryBinding.plan.code[128]? = some (7560, 2594124304) := rfl
theorem room_128 (initial : NativeState) : 128 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_128 : NativeEntryBodyDispatch.Csel3.selected 16#5 16#5 = 2594124304#32 := by decide
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
  have member : (7560, 2594124304) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_128
  have pc : x.regs._PC = MemReloc.imageAddress base 7560 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    128 x inv.core (7560, 2594124304) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (128+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 128 + 4#64 = offset EntryBinding.plan (128+1) from by decide)
  have draws : DefaultState.drawsBefore initial 128 ≤ DefaultState.drawsBefore initial (128+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 128 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_128 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Csel3.selected 16#5 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 16), .lit 0#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Csel3.tailX real x 16#5 16#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_16 real x 16#5 16#5 (by decide) (by decide) (by decide)) next (by simpa only [word_128] using ob)
#print axioms site_128
#print axioms word_128
#print axioms step_128

theorem site_129 : EntryBinding.plan.code[129]? = some (7564, 3943694402) := rfl
theorem room_129 (initial : NativeState) : 129 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_129 : NativeEntryBodyDispatch.SubsShift64.selected 2#5 2#5 0#6 16#5 = 3943694402#32 := by decide
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
  have member : (7564, 3943694402) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_129
  have pc : x.regs._PC = MemReloc.imageAddress base 7564 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    129 x inv.core (7564, 3943694402) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (129+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 129 + 4#64 = offset EntryBinding.plan (129+1) from by decide)
  have draws : DefaultState.drawsBefore initial 129 ≤ DefaultState.drawsBefore initial (129+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 129 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_129 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 2#5 2#5 0#6 16#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨.sbc3, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 2#5 2#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 2#5 2#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_129] using ob)
#print axioms site_129
#print axioms word_129
#print axioms step_129

theorem site_130 : EntryBinding.plan.code[130]? = some (7568, 4196335715) := rfl
theorem room_130 (initial : NativeState) : 130 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_130 : NativeEntryBodyDispatch.Sbcs64.selected 3#5 3#5 = 4196335715#32 := by decide
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
  have member : (7568, 4196335715) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_130
  have pc : x.regs._PC = MemReloc.imageAddress base 7568 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    130 x inv.core (7568, 4196335715) member pc
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
    (NativeEntryBodyDispatch.Sbcs64.selected 3#5 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 3), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64.tailX real x 3#5 3#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_18 real x 3#5 3#5 (by decide) (by decide) (by decide)) next (by simpa only [word_130] using ob)
#print axioms site_130
#print axioms word_130
#print axioms step_130

theorem site_131 : EntryBinding.plan.code[131]? = some (7572, 4196335748) := rfl
theorem room_131 (initial : NativeState) : 131 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_131 : NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5 = 4196335748#32 := by decide
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
  have member : (7572, 4196335748) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_131
  have pc : x.regs._PC = MemReloc.imageAddress base 7572 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    131 x inv.core (7572, 4196335748) member pc
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
    (NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_18 real x 4#5 4#5 (by decide) (by decide) (by decide)) next (by simpa only [word_131] using ob)
#print axioms site_131
#print axioms word_131
#print axioms step_131

theorem site_132 : EntryBinding.plan.code[132]? = some (7576, 3659464869) := rfl
theorem room_132 (initial : NativeState) : 132 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_132 : NativeEntryBodyDispatch.Sbc64.selected 5#5 5#5 = 3659464869#32 := by decide
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
  have member : (7576, 3659464869) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_132
  have pc : x.regs._PC = MemReloc.imageAddress base 7576 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    132 x inv.core (7576, 3659464869) member pc
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
    (NativeEntryBodyDispatch.Sbc64.selected 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Sbc64.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_7 real x 5#5 5#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_132] using ob)
#print axioms site_132
#print axioms word_132
#print axioms step_132

theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (k : Nat) (room : k < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length)
    (selected : k ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132] : List Nat))
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'room) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
#print axioms all_steps

end PipeLean_D234_SecpSqr_c24.DitBodyScalar
