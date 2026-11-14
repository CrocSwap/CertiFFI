import PipeLean_D234_SecpSqr_c25.DitBodyState
import DitShim243.RawFetch
import PipeLean_D234_SecpSqr_c25.DefaultState
import PipeLean_D234_SecpSqr_c25.PairData
import TranslateSpan.DefaultSelectedPairFacts
import TranslateSpan.SecpCurrentEntry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSqr_c25.DitBodyPair

theorem site_0 : EntryBinding.plan.code[0]? = some (7048, 2839555114) := rfl
theorem room_0 (initial : NativeState) : 0 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_0 : NativeEntryBodyDispatch.Ldp8.selected 10#5 1#5 11#5 0#7 = 2839555114#32 := by decide
theorem step_0 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (0+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[0]'(room_0 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[0]? = some (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 1#5 0#7 = (BitVec.addInt (entryGPR initial 1) (0)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 1)) (0) = (BitVec.addInt (entryGPR initial 1) (0))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize X = O := by decide
  have alias := layout.aliases X 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 0)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 1) (0)) = regionVA initial O (8 * 0) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, X, O, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) O 0 mapping (BitVec.addInt (entryGPR initial 1) (0)) := by
    rw [regionAddress]
    exact receipt.spans O 32 0 (by decide) (by rfl) (by decide)
  have binding : DefaultPairSelected.Binding (view EntryBinding.plan mapping initial) O 0 mapping 0#7 1#5 x := by
    unfold DefaultPairSelected.Binding
    rw [source]
    exact span
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) O 0 0#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 0 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 0 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) ≤ DefaultState.drawsBefore initial (0+1) := by
    rw [cost, DefaultState.budget_next_0]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (0+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 0 + 4#64 = offset EntryBinding.plan (0+1) from by decide)
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have memberCode : (7048, 2839555114) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_0
  have codePC : x.regs._PC = MemReloc.imageAddress base 7048 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x inv.core (7048, 2839555114) memberCode codePC
  exact DefaultSelectedPairFacts.ldp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4) 0 (by decide) page (by decide)
    0#7 1#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_0 initial)
    statusBound drawBound (room_0 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next O 0 binding
    [((.x 10), none), ((.x 11), none)] (by decide) (by rfl) (by simpa only [word_0] using ob)
#print axioms site_0
#print axioms word_0
#print axioms step_0

theorem site_1 : EntryBinding.plan.code[1]? = some (7052, 2839622700) := rfl
theorem room_1 (initial : NativeState) : 1 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_1 : NativeEntryBodyDispatch.Ldp8.selected 12#5 1#5 13#5 2#7 = 2839622700#32 := by decide
theorem step_1 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (1+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[1]'(room_1 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[1]? = some (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 1#5 2#7 = (BitVec.addInt (entryGPR initial 1) (16)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 1)) (16) = (BitVec.addInt (entryGPR initial 1) (16))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize X = O := by decide
  have alias := layout.aliases X 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 2)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 1) (16)) = regionVA initial O (8 * 2) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, X, O, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) O 2 mapping (BitVec.addInt (entryGPR initial 1) (16)) := by
    rw [regionAddress]
    exact receipt.spans O 32 2 (by decide) (by rfl) (by decide)
  have binding : DefaultPairSelected.Binding (view EntryBinding.plan mapping initial) O 2 mapping 2#7 1#5 x := by
    unfold DefaultPairSelected.Binding
    rw [source]
    exact span
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) O 2 2#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 1 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 1 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.drawsBefore initial (1+1) := by
    rw [cost, DefaultState.budget_next_1]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (1+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 1 + 4#64 = offset EntryBinding.plan (1+1) from by decide)
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have memberCode : (7052, 2839622700) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_1
  have codePC : x.regs._PC = MemReloc.imageAddress base 7052 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (7052, 2839622700) memberCode codePC
  exact DefaultSelectedPairFacts.ldp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4) 1 (by decide) page (by decide)
    2#7 1#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_1 initial)
    statusBound drawBound (room_1 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next O 2 binding
    [((.x 12), none), ((.x 13), none)] (by decide) (by rfl) (by simpa only [word_1] using ob)
#print axioms site_1
#print axioms word_1
#print axioms step_1

theorem site_133 : EntryBinding.plan.code[133]? = some (7580, 2835352578) := rfl
theorem room_133 (initial : NativeState) : 133 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_133 : NativeEntryBodyDispatch.Stp8.selected 2#5 0#5 3#5 0#7 = 2835352578#32 := by decide
theorem step_133 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 133 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (133+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[133]'(room_133 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_133 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 0#5 0#7 = (BitVec.addInt (entryGPR initial 0) (0)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 0)) (0) = (BitVec.addInt (entryGPR initial 0) (0))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize O = O := by decide
  have alias := layout.aliases O 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 0)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 0) (0)) = regionVA initial O (8 * 0) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, O, O, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) O 0 mapping (BitVec.addInt (entryGPR initial 0) (0)) := by
    rw [regionAddress]
    exact receipt.spans O 32 0 (by decide) (by rfl) (by decide)
  have binding : DefaultPairSelected.Binding (view EntryBinding.plan mapping initial) O 0 mapping 0#7 0#5 x := by
    unfold DefaultPairSelected.Binding
    rw [source]
    exact span
  have targets := SelectedStoreFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) member)
  have output := SecpCurrentEntry.output_safe (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) EntryBinding.plan raw mapping base initial rfl layout
    O 32 0 (by decide) (by decide)
  have facts := DefaultSelectedPairFacts.store_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (rowsFootprint raw.imageRows).byte (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) O 0
    0#7 0#5 x source span targets output
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 133 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 133 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.drawsBefore initial (133+1) := by
    rw [cost, DefaultState.budget_next_133]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (133+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 133 + 4#64 = offset EntryBinding.plan (133+1) from by decide)
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have memberCode : (7580, 2835352578) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_133
  have codePC : x.regs._PC = MemReloc.imageAddress base 7580 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    133 x inv.core (7580, 2835352578) memberCode codePC
  exact DefaultSelectedPairFacts.stp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4) 133 (by decide) page (by decide)
    0#7 0#5 2#5 3#5 (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_133 initial)
    statusBound drawBound (room_133 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next O 0 binding
    (by decide) (by decide) layout.injective
    [] (by decide) (by rfl) (by simpa only [word_133] using ob)
#print axioms site_133
#print axioms word_133
#print axioms step_133

theorem site_134 : EntryBinding.plan.code[134]? = some (7584, 2835420164) := rfl
theorem room_134 (initial : NativeState) : 134 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_134 : NativeEntryBodyDispatch.Stp8.selected 4#5 0#5 5#5 2#7 = 2835420164#32 := by decide
theorem step_134 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 134 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (134+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[134]'(room_134 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_134 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 0#5 2#7 = (BitVec.addInt (entryGPR initial 0) (16)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 0)) (16) = (BitVec.addInt (entryGPR initial 0) (16))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize O = O := by decide
  have alias := layout.aliases O 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 2)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 0) (16)) = regionVA initial O (8 * 2) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, O, O, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) O 2 mapping (BitVec.addInt (entryGPR initial 0) (16)) := by
    rw [regionAddress]
    exact receipt.spans O 32 2 (by decide) (by rfl) (by decide)
  have binding : DefaultPairSelected.Binding (view EntryBinding.plan mapping initial) O 2 mapping 2#7 0#5 x := by
    unfold DefaultPairSelected.Binding
    rw [source]
    exact span
  have targets := SelectedStoreFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) member)
  have output := SecpCurrentEntry.output_safe (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) EntryBinding.plan raw mapping base initial rfl layout
    O 32 2 (by decide) (by decide)
  have facts := DefaultSelectedPairFacts.store_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (rowsFootprint raw.imageRows).byte (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) O 2
    2#7 0#5 x source span targets output
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 134 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 134 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.drawsBefore initial (134+1) := by
    rw [cost, DefaultState.budget_next_134]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (134+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 134 + 4#64 = offset EntryBinding.plan (134+1) from by decide)
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have memberCode : (7584, 2835420164) ∈ EntryBinding.plan.code := List.mem_of_getElem? site_134
  have codePC : x.regs._PC = MemReloc.imageAddress base 7584 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    134 x inv.core (7584, 2835420164) memberCode codePC
  exact DefaultSelectedPairFacts.stp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4) 134 (by decide) page (by decide)
    2#7 0#5 4#5 5#5 (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_134 initial)
    statusBound drawBound (room_134 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next O 2 binding
    (by decide) (by decide) layout.injective
    [] (by decide) (by rfl) (by simpa only [word_134] using ob)
#print axioms site_134
#print axioms word_134
#print axioms step_134

theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (k : Nat) (room : k < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length)
    (selected : k ∈ ([0, 1, 133, 134] : List Nat))
    (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'room) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl
  · exact step_0 real raw config rows mapping base initial topology layout page receipt x inv
  · exact step_1 real raw config rows mapping base initial topology layout page receipt x inv
  · exact step_133 real raw config rows mapping base initial topology layout page receipt x inv
  · exact step_134 real raw config rows mapping base initial topology layout page receipt x inv
#print axioms all_steps

end PipeLean_D234_SecpSqr_c25.DitBodyPair
