import PipeLean_D234_SecpDouble_c12.DefaultState
import PipeLean_D234_SecpDouble_c12.PairData
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
namespace PipeLean_D234_SecpDouble_c12.DefaultPairSites

theorem site_0 : EntryBinding.plan.code[0]? = some (5924, 2839614500) := rfl
theorem room_0 (initial : NativeState) : 0 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_0 : NativeEntryBodyDispatch.Ldp8.selected 4#5 1#5 5#5 2#7 = 2839614500#32 := by decide
theorem step_0 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (0+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[0]'(room_0 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[0]? = some (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 1#5 2#7 = (BitVec.addInt (entryGPR initial 1) (16)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 1)) (16) = (BitVec.addInt (entryGPR initial 1) (16))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize X = X := by decide
  have alias := layout.aliases X 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 2)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 1) (16)) = regionVA initial X (8 * 2) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, X, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 2 mapping (BitVec.addInt (entryGPR initial 1) (16)) := by
    rw [regionAddress]
    exact SecpCurrentEntry.span (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan mapping base initial
      initialInv.core.v1.current queries X 32 2 (by decide) (by rfl) (by decide)
  have binding : DefaultPairSelected.Binding (view EntryBinding.plan mapping initial) X 2 mapping 2#7 1#5 x := by
    unfold DefaultPairSelected.Binding
    rw [source]
    exact span
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 0 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 0 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.drawsBefore initial (0+1) := by
    rw [cost, DefaultState.budget_next_0]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (0+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 0 + 4#64 = offset EntryBinding.plan (0+1) from by decide)
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_0 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.ldp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 0 (by decide) page (by decide)
    2#7 1#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_0 initial)
    statusBound drawBound (room_0 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next X 2 binding
    [((.x 4), none), ((.x 5), none)] (by decide) (by rfl) (by simpa only [word_0] using ob)
#print axioms site_0
#print axioms word_0
#print axioms step_0

theorem site_3 : EntryBinding.plan.code[3]? = some (5936, 2839546914) := rfl
theorem room_3 (initial : NativeState) : 3 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_3 : NativeEntryBodyDispatch.Ldp8.selected 2#5 1#5 3#5 0#7 = 2839546914#32 := by decide
theorem step_3 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 3 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (3+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[3]'(room_3 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[1]? = some (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_3 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 1#5 0#7 = (BitVec.addInt (entryGPR initial 1) (0)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 1)) (0) = (BitVec.addInt (entryGPR initial 1) (0))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize X = X := by decide
  have alias := layout.aliases X 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 0)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 1) (0)) = regionVA initial X (8 * 0) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, X, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 0 mapping (BitVec.addInt (entryGPR initial 1) (0)) := by
    rw [regionAddress]
    exact SecpCurrentEntry.span (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan mapping base initial
      initialInv.core.v1.current queries X 32 0 (by decide) (by rfl) (by decide)
  have binding : DefaultPairSelected.Binding (view EntryBinding.plan mapping initial) X 0 mapping 0#7 1#5 x := by
    unfold DefaultPairSelected.Binding
    rw [source]
    exact span
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_3 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 0 0#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 3 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 3 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) ≤ DefaultState.drawsBefore initial (3+1) := by
    rw [cost, DefaultState.budget_next_3]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (3+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 3 + 4#64 = offset EntryBinding.plan (3+1) from by decide)
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_3 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.ldp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 3 (by decide) page (by decide)
    0#7 1#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_3 initial)
    statusBound drawBound (room_3 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next X 0 binding
    [((.x 2), none), ((.x 3), none)] (by decide) (by rfl) (by simpa only [word_3] using ob)
#print axioms site_3
#print axioms word_3
#print axioms step_3

theorem site_19 : EntryBinding.plan.code[19]? = some (6000, 2835352578) := rfl
theorem room_19 (initial : NativeState) : 19 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_19 : NativeEntryBodyDispatch.Stp8.selected 2#5 0#5 3#5 0#7 = 2835352578#32 := by decide
theorem step_19 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 19 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (19+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[19]'(room_19 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_19 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
    exact SecpCurrentEntry.span (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan mapping base initial
      initialInv.core.v1.current queries O 32 0 (by decide) (by rfl) (by decide)
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
  have statusBound : DefaultState.drawsBefore initial 19 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 19 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.drawsBefore initial (19+1) := by
    rw [cost, DefaultState.budget_next_19]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (19+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 19 + 4#64 = offset EntryBinding.plan (19+1) from by decide)
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_19 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.stp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 19 (by decide) page (by decide)
    0#7 0#5 2#5 3#5 (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_19 initial)
    statusBound drawBound (room_19 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next O 0 binding
    (by decide) (by decide) layout.injective
    [] (by decide) (by rfl) (by simpa only [word_19] using ob)
#print axioms site_19
#print axioms word_19
#print axioms step_19

theorem site_20 : EntryBinding.plan.code[20]? = some (6004, 2835420164) := rfl
theorem room_20 (initial : NativeState) : 20 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_20 : NativeEntryBodyDispatch.Stp8.selected 4#5 0#5 5#5 2#7 = 2835420164#32 := by decide
theorem step_20 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 20 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (20+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[20]'(room_20 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_20 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
    exact SecpCurrentEntry.span (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan mapping base initial
      initialInv.core.v1.current queries O 32 2 (by decide) (by rfl) (by decide)
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
  have statusBound : DefaultState.drawsBefore initial 20 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 20 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.drawsBefore initial (20+1) := by
    rw [cost, DefaultState.budget_next_20]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (20+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 20 + 4#64 = offset EntryBinding.plan (20+1) from by decide)
  have compiles : (ValuePlan.compileRun .g regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (G.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_20 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.stp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 20 (by decide) page (by decide)
    2#7 0#5 4#5 5#5 (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .g (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_20 initial)
    statusBound drawBound (room_20 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next O 2 binding
    (by decide) (by decide) layout.injective
    [] (by decide) (by rfl) (by simpa only [word_20] using ob)
#print axioms site_20
#print axioms word_20
#print axioms step_20

theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (k : Nat) (room : k < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length)
    (selected : k ∈ ([0, 3, 19, 20] : List Nat))
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .g (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'room) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl
  · exact step_0 real raw config rows mapping base initial catalogue topology layout page checked x inv
  · exact step_3 real raw config rows mapping base initial catalogue topology layout page checked x inv
  · exact step_19 real raw config rows mapping base initial catalogue topology layout page checked x inv
  · exact step_20 real raw config rows mapping base initial catalogue topology layout page checked x inv
#print axioms all_steps

end PipeLean_D234_SecpDouble_c12.DefaultPairSites
