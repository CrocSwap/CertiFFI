import PipeLean_D234_SecpNeg_c11.DefaultState
import ArmCertValueTail.Movz64z
import ArmCertValueTail.OrrImm32_0
import ArmCertValueTail.Sbcs64Reg
import ArmCertValueTail.SecpCsinv0ZZ
import ArmCertValueTail.SecpOrr64
import ArmCertValueTail.SecpSbc64
import ArmCertValueTail.SubsShift64
import N1D226.BicRuntime.DriverValue
import N1D226.CmpShiftZero64.Value
import TranslateScalarTagCheck.Runtime
import TranslateScalarTagCheck.Secp
import TranslateScalarTagCheck.Tails
import TranslateSpan.DefaultScalar
import TranslateSpan.LegacyScalarEffects
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpNeg_c11.DefaultScalarSites

theorem site_1 : EntryBinding.plan.code[1]? = some (5860, 2852388967) := rfl
theorem room_1 (initial : NativeState) : 1 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_1 : NativeEntryBodyDispatch.SecpOrr64.selected 7#5 3#5 4#5 = 2852388967#32 := by decide
theorem step_1 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (1+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[1]'(room_1 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5860, 2852388967) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_1
  have pc : x.regs._PC = MemReloc.imageAddress base 5860 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (5860, 2852388967) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (1+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 1 + 4#64 = offset EntryBinding.plan (1+1) from by decide)
  have draws : DefaultState.drawsBefore initial 1 ≤ DefaultState.drawsBefore initial (1+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 1 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_1 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpOrr64.selected 7#5 3#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨(.orr), [.reg (.x 3), .reg (.x 4)]⟩)] (none) x inv
    (ArmCertValue.SecpOrr64.tailX real x 7#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_13 real x 7#5 3#5 4#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide))
    (by
      intro fin run vh memory
      exact TranslateSpan.LegacyScalarEffects.orr_zero_effect .g (view EntryBinding.plan mapping initial) regions_c00
        (.x 7) (.reg (.x 3)) (.reg (.x 4)) x fin vh memory)
    next (by simpa only [word_1] using ob)
#print axioms site_1
#print axioms word_1
#print axioms step_1

theorem site_3 : EntryBinding.plan.code[3]? = some (5868, 2852454631) := rfl
theorem room_3 (initial : NativeState) : 3 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_3 : NativeEntryBodyDispatch.SecpOrr64.selected 7#5 7#5 5#5 = 2852454631#32 := by decide
theorem step_3 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 3 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (3+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[3]'(room_3 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5868, 2852454631) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 5868 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (5868, 2852454631) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (3+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 3 + 4#64 = offset EntryBinding.plan (3+1) from by decide)
  have draws : DefaultState.drawsBefore initial 3 ≤ DefaultState.drawsBefore initial (3+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_effect_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 3 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_3 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpOrr64.selected 7#5 7#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨(.orr), [.reg (.x 7), .reg (.x 5)]⟩)] (none) x inv
    (ArmCertValue.SecpOrr64.tailX real x 7#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_13 real x 7#5 7#5 5#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide))
    (by
      intro fin run vh memory
      exact TranslateSpan.LegacyScalarEffects.orr_zero_effect .g (view EntryBinding.plan mapping initial) regions_c00
        (.x 7) (.reg (.x 7)) (.reg (.x 5)) x fin vh memory)
    next (by simpa only [word_3] using ob)
#print axioms site_3
#print axioms word_3
#print axioms step_3

theorem site_4 : EntryBinding.plan.code[4]? = some (5872, 2852520167) := rfl
theorem room_4 (initial : NativeState) : 4 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_4 : NativeEntryBodyDispatch.SecpOrr64.selected 7#5 7#5 6#5 = 2852520167#32 := by decide
theorem step_4 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (4+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[4]'(room_4 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5872, 2852520167) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 5872 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (5872, 2852520167) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 4 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_4 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpOrr64.selected 7#5 7#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨(.orr), [.reg (.x 7), .reg (.x 6)]⟩)] (none) x inv
    (ArmCertValue.SecpOrr64.tailX real x 7#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_13 real x 7#5 7#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide))
    (by
      intro fin run vh memory
      exact TranslateSpan.LegacyScalarEffects.orr_zero_effect .g (view EntryBinding.plan mapping initial) regions_c00
        (.x 7) (.reg (.x 7)) (.reg (.x 6)) x fin vh memory)
    next (by simpa only [word_4] using ob)
#print axioms site_4
#print axioms word_4
#print axioms step_4

theorem site_5 : EntryBinding.plan.code[5]? = some (5876, 3944677631) := rfl
theorem room_5 (initial : NativeState) : 5 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_5 : N1D226.CmpShiftZero64.Encoding.selected 7#5 0#6 = 3944677631#32 := by decide
theorem step_5 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (5+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[5]'(room_5 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5876, 3944677631) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 5876 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (5876, 3944677631) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 5 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_5 initial) compiles page (by decide)
    (N1D226.CmpShiftZero64.Encoding.selected 7#5 0#6) _ _ (fun s => s.regs._PC + 4#64)
    [] (some (⟨.sbc3N, [.reg (.x 7), .lit 0#64, .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 7), .lit 0#64, .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 7), .lit 0#64, .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 7), .lit 0#64, .lit 1#64]⟩)) (by rfl) x inv
    (N1D226.CmpShiftZero64.Value.tailX real x 7#5 0#6 (by decide)) (TranslateScalarTagCheck.Runtime.tail_7 real x 7#5 0#6 (by decide)) next (by simpa only [word_5] using ob)
#print axioms site_5
#print axioms word_5
#print axioms step_5

theorem site_6 : EntryBinding.plan.code[6]? = some (5880, 3667854306) := rfl
theorem room_6 (initial : NativeState) : 6 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_6 : NativeEntryBodyDispatch.SecpCsinv0ZZ.selected 2#5 = 3667854306#32 := by decide
theorem step_6 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 6 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (6+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[6]'(room_6 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5880, 3667854306) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 5880 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (5880, 3667854306) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 6 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_6 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected 2#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 2), some ⟨(.cselc 0#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpCsinv0ZZ.tailX real x 2#5 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_1 real x 2#5 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_6] using ob)
#print axioms site_6
#print axioms word_6
#print axioms step_6

theorem site_7 : EntryBinding.plan.code[7]? = some (5884, 3531635207) := rfl
theorem room_7 (initial : NativeState) : 7 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_7 : NativeEntryBodyDispatch.Movz64z.selected 7#5 976#16 = 3531635207#32 := by decide
theorem step_7 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 7 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (7+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[7]'(room_7 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5884, 3531635207) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 5884 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (5884, 3531635207) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 7 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_7 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Movz64z.selected 7#5 976#16) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨(.const 976#64), []⟩)] (none) (by rfl) x inv
    (ArmCertValue.Movz64z.tailX real x 7#5 976#16 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_2 real x 7#5 976#16 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_7] using ob)
#print axioms site_7
#print axioms word_7
#print axioms step_7

theorem site_8 : EntryBinding.plan.code[8]? = some (5888, 2992636135) := rfl
theorem room_8 (initial : NativeState) : 8 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_8 : NativeEntryBodyDispatch.OrrImm32_0.selected 7#5 7#5 = 2992636135#32 := by decide
theorem step_8 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 8 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (8+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[8]'(room_8 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5888, 2992636135) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 5888 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (5888, 2992636135) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 8 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_8 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.OrrImm32_0.selected 7#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.orr, [.reg (.x 7), .lit 4294967296#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.OrrImm32_0.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_8 real x 7#5 7#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_8] using ob)
#print axioms site_8
#print axioms word_8
#print axioms step_8

theorem site_9 : EntryBinding.plan.code[9]? = some (5892, 2317811783) := rfl
theorem room_9 (initial : NativeState) : 9 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_9 : N1D226.BicRuntime.DriverValue.selected 7#5 2#5 7#5 = 2317811783#32 := by decide
theorem step_9 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 9 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (9+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[9]'(room_9 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5892, 2317811783) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 5892 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (5892, 2317811783) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 9 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_9 initial) compiles page (by decide)
    (N1D226.BicRuntime.DriverValue.selected 7#5 2#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    (N1D226.BicRuntime.DriverValue.upd x 7#5 2#5 7#5) (none) x inv
    (N1D226.BicRuntime.DriverValue.tailX real x 7#5 2#5 7#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Runtime.tail_0 real x 7#5 2#5 0#6 7#5 (by decide) (by decide) (by decide))
    (by
      intro fin run vh memory
      exact N1D226.BicRuntime.DriverValue.holds_of_native (view EntryBinding.plan mapping initial) regions_c00 x fin 7#5 2#5 7#5 vh memory)
    next (by simpa only [word_9] using ob)
#print axioms site_9
#print axioms word_9
#print axioms step_9

theorem site_10 : EntryBinding.plan.code[10]? = some (5896, 3942842595) := rfl
theorem room_10 (initial : NativeState) : 10 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_10 : NativeEntryBodyDispatch.SubsShift64.selected 3#5 7#5 0#6 3#5 = 3942842595#32 := by decide
theorem step_10 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 10 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (10+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[10]'(room_10 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5896, 3942842595) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 5896 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (5896, 3942842595) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 10 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_10 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 3#5 7#5 0#6 3#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 7), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 3), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 3#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 3#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_10] using ob)
#print axioms site_10
#print axioms word_10
#print axioms step_10

theorem site_11 : EntryBinding.plan.code[11]? = some (5900, 4194566212) := rfl
theorem room_11 (initial : NativeState) : 11 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_11 : NativeEntryBodyDispatch.Sbcs64Reg.selected 4#5 2#5 4#5 = 4194566212#32 := by decide
theorem step_11 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 11 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (11+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[11]'(room_11 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5900, 4194566212) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 5900 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (5900, 4194566212) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 11 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_11 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64Reg.selected 4#5 2#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 2), .reg (.x 4), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 2), .reg (.x 4), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 2), .reg (.x 4), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 2), .reg (.x 4), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 2), .reg (.x 4), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64Reg.tailX real x 4#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_0 real x 4#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_11] using ob)
#print axioms site_11
#print axioms word_11
#print axioms step_11

theorem site_12 : EntryBinding.plan.code[12]? = some (5904, 4194631749) := rfl
theorem room_12 (initial : NativeState) : 12 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_12 : NativeEntryBodyDispatch.Sbcs64Reg.selected 5#5 2#5 5#5 = 4194631749#32 := by decide
theorem step_12 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 12 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (12+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[12]'(room_12 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5904, 4194631749) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 5904 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (5904, 4194631749) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (12+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 12 + 4#64 = offset EntryBinding.plan (12+1) from by decide)
  have draws : DefaultState.drawsBefore initial 12 ≤ DefaultState.drawsBefore initial (12+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 12 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_12 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64Reg.selected 5#5 2#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 2), .reg (.x 5), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 2), .reg (.x 5), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 2), .reg (.x 5), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 2), .reg (.x 5), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 2), .reg (.x 5), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64Reg.tailX real x 5#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_0 real x 5#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_12] using ob)
#print axioms site_12
#print axioms word_12
#print axioms step_12

theorem site_13 : EntryBinding.plan.code[13]? = some (5908, 3657826374) := rfl
theorem room_13 (initial : NativeState) : 13 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_13 : NativeEntryBodyDispatch.SecpSbc64.selected 6#5 2#5 6#5 = 3657826374#32 := by decide
theorem step_13 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 13 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (13+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[13]'(room_13 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (5908, 3657826374) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 5908 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (5908, 3657826374) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 13 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_13 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SecpSbc64.selected 6#5 2#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 2), .reg (.x 6), .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.SecpSbc64.tailX real x 6#5 2#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Secp.tail_14 real x 6#5 2#5 6#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_13] using ob)
#print axioms site_13
#print axioms word_13
#print axioms step_13

theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (k : Nat) (room : k < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length)
    (selected : k ∈ ([1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List Nat))
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'room) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_1 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_3 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_4 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_5 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_6 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_7 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_8 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_9 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_10 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_11 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_12 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_13 real raw config rows mapping base initial catalogue topology layout page x inv
#print axioms all_steps

end PipeLean_D234_SecpNeg_c11.DefaultScalarSites
