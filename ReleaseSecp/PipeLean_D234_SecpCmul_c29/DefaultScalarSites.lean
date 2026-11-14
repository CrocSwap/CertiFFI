import PipeLean_D234_SecpCmul_c29.DefaultState
import ArmCertValueTail.Adcs64
import ArmCertValueTail.Adcs64ZRm
import ArmCertValueTail.AddImm64
import ArmCertValueTail.AddsShift64
import ArmCertValueTail.Csel3
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
namespace PipeLean_D234_SecpCmul_c29.DefaultScalarSites

theorem site_2 : EntryBinding.plan.code[2]? = some (7916, 2600959011) := rfl
theorem room_2 (initial : NativeState) : 2 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_2 : NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 7#5 = 2600959011#32 := by decide
theorem step_2 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 2 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (2+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[2]'(room_2 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7916, 2600959011) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 7916 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (7916, 2600959011) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 2 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_2 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 1), .reg (.x 7)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 3#5 1#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 3#5 1#5 7#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_2] using ob)
#print axioms site_2
#print axioms word_2
#print axioms step_2

theorem site_3 : EntryBinding.plan.code[3]? = some (7920, 2601024548) := rfl
theorem room_3 (initial : NativeState) : 3 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_3 : NativeEntryBodyDispatch.Madd64.selected 4#5 1#5 8#5 = 2601024548#32 := by decide
theorem step_3 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 3 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (3+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[3]'(room_3 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7920, 2601024548) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 7920 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (7920, 2601024548) member pc
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (3+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 3 + 4#64 = offset EntryBinding.plan (3+1) from by decide)
  have draws : DefaultState.drawsBefore initial 3 ≤ DefaultState.drawsBefore initial (3+1) :=
    Nat.le_refl _
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  exact DefaultMTE2.class_next_frame real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 3 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_3 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 4#5 1#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 1), .reg (.x 8)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 4#5 1#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 4#5 1#5 8#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_3] using ob)
#print axioms site_3
#print axioms word_3
#print axioms step_3

theorem site_4 : EntryBinding.plan.code[4]? = some (7924, 2601090085) := rfl
theorem room_4 (initial : NativeState) : 4 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_4 : NativeEntryBodyDispatch.Madd64.selected 5#5 1#5 9#5 = 2601090085#32 := by decide
theorem step_4 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (4+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[4]'(room_4 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7924, 2601090085) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 7924 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (7924, 2601090085) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 4 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_4 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 5#5 1#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.mul, [.reg (.x 1), .reg (.x 9)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 5#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 5#5 1#5 9#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_4] using ob)
#print axioms site_4
#print axioms word_4
#print axioms step_4

theorem site_5 : EntryBinding.plan.code[5]? = some (7928, 2601155622) := rfl
theorem room_5 (initial : NativeState) : 5 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_5 : NativeEntryBodyDispatch.Madd64.selected 6#5 1#5 10#5 = 2601155622#32 := by decide
theorem step_5 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (5+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[5]'(room_5 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7928, 2601155622) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 7928 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (7928, 2601155622) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 5 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_5 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 6#5 1#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.mul, [.reg (.x 1), .reg (.x 10)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 6#5 1#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 6#5 1#5 10#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_5] using ob)
#print axioms site_5
#print axioms word_5
#print axioms step_5

theorem site_6 : EntryBinding.plan.code[6]? = some (7932, 2613541927) := rfl
theorem room_6 (initial : NativeState) : 6 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_6 : NativeEntryBodyDispatch.Umulh64.selected 7#5 1#5 7#5 = 2613541927#32 := by decide
theorem step_6 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 6 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (6+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[6]'(room_6 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7932, 2613541927) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 7932 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (7932, 2613541927) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 6 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_6 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 7#5 1#5 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 1), .reg (.x 7)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 7#5 1#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 7#5 1#5 7#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_6] using ob)
#print axioms site_6
#print axioms word_6
#print axioms step_6

theorem site_7 : EntryBinding.plan.code[7]? = some (7936, 2613607464) := rfl
theorem room_7 (initial : NativeState) : 7 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_7 : NativeEntryBodyDispatch.Umulh64.selected 8#5 1#5 8#5 = 2613607464#32 := by decide
theorem step_7 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 7 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (7+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[7]'(room_7 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7936, 2613607464) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 7936 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (7936, 2613607464) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 7 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_7 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 8#5 1#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 1), .reg (.x 8)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 8#5 1#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 8#5 1#5 8#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_7] using ob)
#print axioms site_7
#print axioms word_7
#print axioms step_7

theorem site_8 : EntryBinding.plan.code[8]? = some (7940, 2613673001) := rfl
theorem room_8 (initial : NativeState) : 8 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_8 : NativeEntryBodyDispatch.Umulh64.selected 9#5 1#5 9#5 = 2613673001#32 := by decide
theorem step_8 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 8 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (8+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[8]'(room_8 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7940, 2613673001) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 7940 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (7940, 2613673001) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 8 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_8 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 9#5 1#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 1), .reg (.x 9)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 9#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 9#5 1#5 9#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_8] using ob)
#print axioms site_8
#print axioms word_8
#print axioms step_8

theorem site_9 : EntryBinding.plan.code[9]? = some (7944, 2613738538) := rfl
theorem room_9 (initial : NativeState) : 9 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_9 : NativeEntryBodyDispatch.Umulh64.selected 10#5 1#5 10#5 = 2613738538#32 := by decide
theorem step_9 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 9 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (9+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[9]'(room_9 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7944, 2613738538) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 7944 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (7944, 2613738538) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 9 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_9 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 10#5 1#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 1), .reg (.x 10)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 10#5 1#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 10#5 1#5 10#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_9] using ob)
#print axioms site_9
#print axioms word_9
#print axioms step_9

theorem site_10 : EntryBinding.plan.code[10]? = some (7948, 2869362820) := rfl
theorem room_10 (initial : NativeState) : 10 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_10 : NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 7#5 = 2869362820#32 := by decide
theorem step_10 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 10 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (10+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[10]'(room_10 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7948, 2869362820) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 7948 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (7948, 2869362820) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 10 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_10 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 4#5 4#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 4#5 4#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_10] using ob)
#print axioms site_10
#print axioms word_10
#print axioms step_10

theorem site_11 : EntryBinding.plan.code[11]? = some (7952, 3121086629) := rfl
theorem room_11 (initial : NativeState) : 11 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_11 : NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5 = 3121086629#32 := by decide
theorem step_11 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 11 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (11+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[11]'(room_11 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7952, 3121086629) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 7952 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (7952, 3121086629) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 11 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_11 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_11] using ob)
#print axioms site_11
#print axioms word_11
#print axioms step_11

theorem site_12 : EntryBinding.plan.code[12]? = some (7956, 3121152198) := rfl
theorem room_12 (initial : NativeState) : 12 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_12 : NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 9#5 = 3121152198#32 := by decide
theorem step_12 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 12 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (12+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[12]'(room_12 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7956, 3121152198) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 7956 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (7956, 3121152198) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 12 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_12 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_12] using ob)
#print axioms site_12
#print axioms word_12
#print axioms step_12

theorem site_13 : EntryBinding.plan.code[13]? = some (7960, 3122594122) := rfl
theorem room_13 (initial : NativeState) : 13 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_13 : NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5 = 3122594122#32 := by decide
theorem step_13 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 13 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (13+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[13]'(room_13 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7960, 3122594122) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 7960 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (7960, 3122594122) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 13 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_13 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 10#5 10#5 (by decide) (by decide) (by decide)) next (by simpa only [word_13] using ob)
#print axioms site_13
#print axioms word_13
#print axioms step_13

theorem site_14 : EntryBinding.plan.code[14]? = some (7964, 2432697674) := rfl
theorem room_14 (initial : NativeState) : 14 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_14 : NativeEntryBodyDispatch.AddImm64.selected 10#5 10#5 1#12 = 2432697674#32 := by decide
theorem step_14 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 14 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (14+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[14]'(room_14 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7964, 2432697674) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 7964 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (7964, 2432697674) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 14 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_14 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddImm64.selected 10#5 10#5 1#12) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 10), some ⟨.add, [.reg (.x 10), .lit 1#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.AddImm64.tailX real x 10#5 10#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) (TranslateScalarTagCheck.Tails.tail_1 real x 10#5 10#5 1#12 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_14] using ob)
#print axioms site_14
#print axioms word_14
#print axioms step_14

theorem site_15 : EntryBinding.plan.code[15]? = some (7968, 3531635241) := rfl
theorem room_15 (initial : NativeState) : 15 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_15 : NativeEntryBodyDispatch.Movz64z.selected 9#5 977#16 = 3531635241#32 := by decide
theorem step_15 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 15 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (15+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[15]'(room_15 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7968, 3531635241) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_15
  have pc : x.regs._PC = MemReloc.imageAddress base 7968 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (7968, 3531635241) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 15 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_15 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Movz64z.selected 9#5 977#16) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨(.const 977#64), []⟩)] (none) (by rfl) x inv
    (ArmCertValue.Movz64z.tailX real x 9#5 977#16 (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_2 real x 9#5 977#16 (by decide) ⟨⟩ (by decide)) next (by simpa only [word_15] using ob)
#print axioms site_15
#print axioms word_15
#print axioms step_15

theorem site_16 : EntryBinding.plan.code[16]? = some (7972, 2992636201) := rfl
theorem room_16 (initial : NativeState) : 16 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_16 : NativeEntryBodyDispatch.OrrImm32_0.selected 9#5 9#5 = 2992636201#32 := by decide
theorem step_16 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 16 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (16+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[16]'(room_16 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7972, 2992636201) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 7972 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (7972, 2992636201) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 16 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_16 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.OrrImm32_0.selected 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨.orr, [.reg (.x 9), .lit 4294967296#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.OrrImm32_0.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_8 real x 9#5 9#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_16] using ob)
#print axioms site_16
#print axioms word_16
#print axioms step_16

theorem site_17 : EntryBinding.plan.code[17]? = some (7976, 2601090375) := rfl
theorem room_17 (initial : NativeState) : 17 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_17 : NativeEntryBodyDispatch.Madd64.selected 7#5 10#5 9#5 = 2601090375#32 := by decide
theorem step_17 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 17 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (17+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[17]'(room_17 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7976, 2601090375) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 7976 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (7976, 2601090375) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 17 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_17 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Madd64.selected 7#5 10#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 10), .reg (.x 9)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Madd64.tailX real x 7#5 10#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_3 real x 7#5 10#5 9#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_17] using ob)
#print axioms site_17
#print axioms word_17
#print axioms step_17

theorem site_18 : EntryBinding.plan.code[18]? = some (7980, 2613673288) := rfl
theorem room_18 (initial : NativeState) : 18 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_18 : NativeEntryBodyDispatch.Umulh64.selected 8#5 10#5 9#5 = 2613673288#32 := by decide
theorem step_18 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 18 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (18+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[18]'(room_18 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7980, 2613673288) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 7980 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (7980, 2613673288) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 18 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_18 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Umulh64.selected 8#5 10#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 10), .reg (.x 9)]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Umulh64.tailX real x 8#5 10#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_4 real x 8#5 10#5 9#5 (by decide) (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_18] using ob)
#print axioms site_18
#print axioms word_18
#print axioms step_18

theorem site_19 : EntryBinding.plan.code[19]? = some (7984, 2869362787) := rfl
theorem room_19 (initial : NativeState) : 19 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_19 : NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 7#5 = 2869362787#32 := by decide
theorem step_19 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 19 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (19+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[19]'(room_19 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7984, 2869362787) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 7984 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (7984, 2869362787) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 19 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_19 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 7#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩)) (by rfl) x inv
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_14 real x 3#5 3#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_19] using ob)
#print axioms site_19
#print axioms word_19
#print axioms step_19

theorem site_20 : EntryBinding.plan.code[20]? = some (7988, 3121086596) := rfl
theorem room_20 (initial : NativeState) : 20 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_20 : NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 8#5 = 3121086596#32 := by decide
theorem step_20 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 20 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (20+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[20]'(room_20 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7988, 3121086596) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 7988 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (7988, 3121086596) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 20 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_20 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 8#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_12 real x 4#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_20] using ob)
#print axioms site_20
#print axioms word_20
#print axioms step_20

theorem site_21 : EntryBinding.plan.code[21]? = some (7992, 3122593957) := rfl
theorem room_21 (initial : NativeState) : 21 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_21 : NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5 = 3122593957#32 := by decide
theorem step_21 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 21 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (21+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[21]'(room_21 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7992, 3122593957) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 7992 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (7992, 3122593957) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 21 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_21 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 5#5 5#5 (by decide) (by decide) (by decide)) next (by simpa only [word_21] using ob)
#print axioms site_21
#print axioms word_21
#print axioms step_21

theorem site_22 : EntryBinding.plan.code[22]? = some (7996, 3122593990) := rfl
theorem room_22 (initial : NativeState) : 22 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_22 : NativeEntryBodyDispatch.Adcs64ZRm.selected 6#5 6#5 = 3122593990#32 := by decide
theorem step_22 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 22 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (22+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[22]'(room_22 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (7996, 3122593990) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 7996 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (7996, 3122593990) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 22 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_22 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Adcs64ZRm.selected 6#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Adcs64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_13 real x 6#5 6#5 (by decide) (by decide) (by decide)) next (by simpa only [word_22] using ob)
#print axioms site_22
#print axioms word_22
#print axioms step_22

theorem site_23 : EntryBinding.plan.code[23]? = some (8000, 2594124073) := rfl
theorem room_23 (initial : NativeState) : 23 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_23 : NativeEntryBodyDispatch.Csel3.selected 9#5 9#5 = 2594124073#32 := by decide
theorem step_23 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 23 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (23+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[23]'(room_23 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (8000, 2594124073) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 8000 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (8000, 2594124073) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 23 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_23 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Csel3.selected 9#5 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 9), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 9), .lit 0#64]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Csel3.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_16 real x 9#5 9#5 (by decide) (by decide) (by decide)) next (by simpa only [word_23] using ob)
#print axioms site_23
#print axioms word_23
#print axioms step_23

theorem site_24 : EntryBinding.plan.code[24]? = some (8004, 3943235683) := rfl
theorem room_24 (initial : NativeState) : 24 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_24 : NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 9#5 = 3943235683#32 := by decide
theorem step_24 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 24 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (24+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[24]'(room_24 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (8004, 3943235683) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 8004 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (8004, 3943235683) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 24 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_24 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 9#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩)) (by rfl) x inv
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_15 real x 3#5 3#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide)) next (by simpa only [word_24] using ob)
#print axioms site_24
#print axioms word_24
#print axioms step_24

theorem site_25 : EntryBinding.plan.code[25]? = some (8008, 4196335748) := rfl
theorem room_25 (initial : NativeState) : 25 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_25 : NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5 = 4196335748#32 := by decide
theorem step_25 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 25 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (25+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[25]'(room_25 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (8008, 4196335748) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_25
  have pc : x.regs._PC = MemReloc.imageAddress base 8008 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    25 x inv.core (8008, 4196335748) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 25 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_25 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_18 real x 4#5 4#5 (by decide) (by decide) (by decide)) next (by simpa only [word_25] using ob)
#print axioms site_25
#print axioms word_25
#print axioms step_25

theorem site_26 : EntryBinding.plan.code[26]? = some (8012, 4196335781) := rfl
theorem room_26 (initial : NativeState) : 26 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_26 : NativeEntryBodyDispatch.Sbcs64.selected 5#5 5#5 = 4196335781#32 := by decide
theorem step_26 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 26 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (26+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[26]'(room_26 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (8012, 4196335781) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_26
  have pc : x.regs._PC = MemReloc.imageAddress base 8012 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    26 x inv.core (8012, 4196335781) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 26 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_26 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbcs64.selected 5#5 5#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) (by rfl) x inv
    (ArmCertValue.Sbcs64.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) (TranslateScalarTagCheck.Tails.tail_18 real x 5#5 5#5 (by decide) (by decide) (by decide)) next (by simpa only [word_26] using ob)
#print axioms site_26
#print axioms word_26
#print axioms step_26

theorem site_27 : EntryBinding.plan.code[27]? = some (8016, 3659464902) := rfl
theorem room_27 (initial : NativeState) : 27 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_27 : NativeEntryBodyDispatch.Sbc64.selected 6#5 6#5 = 3659464902#32 := by decide
theorem step_27 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 27 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (27+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[27]'(room_27 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have member : (8016, 3659464902) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 8016 := by
    rw [inv.core.v1.pc]; rfl
  have ob := SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (8016, 3659464902) member pc
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
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable)) base (offset EntryBinding.plan) EntryBinding.plan.code.length
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue 27 initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) draws (by decide)
    (room_27 initial) compiles page (by decide)
    (NativeEntryBodyDispatch.Sbc64.selected 6#5 6#5) _ _ (fun s => s.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) (by rfl) x inv
    (ArmCertValue.Sbc64.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) (TranslateScalarTagCheck.Tails.tail_7 real x 6#5 6#5 (by decide) (by decide) ⟨⟩ (by decide)) next (by simpa only [word_27] using ob)
#print axioms site_27
#print axioms word_27
#print axioms step_27

theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (k : Nat) (room : k < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length)
    (selected : k ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List Nat))
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'room) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_2 real raw config rows mapping base initial catalogue topology layout page x inv
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
  · exact step_14 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_15 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_16 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_17 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_18 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_19 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_20 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_21 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_22 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_23 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_24 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_25 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_26 real raw config rows mapping base initial catalogue topology layout page x inv
  · exact step_27 real raw config rows mapping base initial catalogue topology layout page x inv
#print axioms all_steps

end PipeLean_D234_SecpCmul_c29.DefaultScalarSites
