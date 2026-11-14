import PipeLean_D234_SecpAdd_c01.DefaultState
import PipeLean_D234_SecpAdd_c01.PairData
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
namespace PipeLean_D234_SecpAdd_c01.DefaultPairSites

theorem site_0 : EntryBinding.plan.code[0]? = some (5688, 2839549989) := rfl
theorem room_0 (initial : NativeState) : 0 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_0 : NativeEntryBodyDispatch.Ldp8.selected 5#5 1#5 6#5 0#7 = 2839549989#32 := by decide
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
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[0]'(room_0 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
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
  obtain ⟨data,payload⟩ := PairData.load_payload_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 0 0#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 0 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 0 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) ≤ DefaultState.drawsBefore initial (0+1) := by
    rw [cost, DefaultState.budget_next_0]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (0+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 0 + 4#64 = offset EntryBinding.plan (0+1) from by decide)
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_0 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.ldp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 0 (by decide) page (by decide)
    0#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_0 initial)
    statusBound drawBound (room_0 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next X 0 binding
    [((.x 5), none), ((.x 6), none)] (by decide) (by rfl) (by simpa only [word_0] using ob)
#print axioms site_0
#print axioms word_0
#print axioms step_0

theorem site_1 : EntryBinding.plan.code[1]? = some (5692, 2839546948) := rfl
theorem room_1 (initial : NativeState) : 1 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_1 : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 0#7 = 2839546948#32 := by decide
theorem step_1 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (1+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[1]'(room_1 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[1]? = some (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 2) 0 = entryGPR initial 2 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 2 (by decide)
  have pointer := PairData.memory_base_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 2#5 0#7 = (BitVec.addInt (entryGPR initial 2) (0)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 2)) (0) = (BitVec.addInt (entryGPR initial 2) (0))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize Y = X := by decide
  have alias := layout.aliases Y 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 0)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 2) (0)) = regionVA initial X (8 * 0) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, Y, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 0 mapping (BitVec.addInt (entryGPR initial 2) (0)) := by
    rw [regionAddress]
    exact SecpCurrentEntry.span (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan mapping base initial
      initialInv.core.v1.current queries X 32 0 (by decide) (by rfl) (by decide)
  have binding : DefaultPairSelected.Binding (view EntryBinding.plan mapping initial) X 0 mapping 0#7 2#5 x := by
    unfold DefaultPairSelected.Binding
    rw [source]
    exact span
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 0 0#7 2#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 1 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 1 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) ≤ DefaultState.drawsBefore initial (1+1) := by
    rw [cost, DefaultState.budget_next_1]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (1+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 1 + 4#64 = offset EntryBinding.plan (1+1) from by decide)
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_1 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.ldp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 1 (by decide) page (by decide)
    0#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_1 initial)
    statusBound drawBound (room_1 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next X 0 binding
    [((.x 4), none), ((.x 3), none)] (by decide) (by rfl) (by simpa only [word_1] using ob)
#print axioms site_1
#print axioms word_1
#print axioms step_1

theorem site_4 : EntryBinding.plan.code[4]? = some (5704, 2839617575) := rfl
theorem room_4 (initial : NativeState) : 4 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_4 : NativeEntryBodyDispatch.Ldp8.selected 7#5 1#5 8#5 2#7 = 2839617575#32 := by decide
theorem step_4 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (4+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[4]'(room_4 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_4 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  obtain ⟨data,payload⟩ := PairData.load_payload_4 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 4 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 4 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.drawsBefore initial (4+1) := by
    rw [cost, DefaultState.budget_next_4]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (4+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 4 + 4#64 = offset EntryBinding.plan (4+1) from by decide)
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_4 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.ldp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 4 (by decide) page (by decide)
    2#7 1#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_4 initial)
    statusBound drawBound (room_4 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next X 2 binding
    [((.x 7), none), ((.x 8), none)] (by decide) (by rfl) (by simpa only [word_4] using ob)
#print axioms site_4
#print axioms word_4
#print axioms step_4

theorem site_5 : EntryBinding.plan.code[5]? = some (5708, 2839612484) := rfl
theorem room_5 (initial : NativeState) : 5 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_5 : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 2#7 = 2839612484#32 := by decide
theorem step_5 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (5+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[5]'(room_5 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 2) 0 = entryGPR initial 2 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 2 (by decide)
  have pointer := PairData.memory_base_5 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 2#5 2#7 = (BitVec.addInt (entryGPR initial 2) (16)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 2)) (16) = (BitVec.addInt (entryGPR initial 2) (16))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize Y = X := by decide
  have alias := layout.aliases Y 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 2)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 2) (16)) = regionVA initial X (8 * 2) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, Y, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 2 mapping (BitVec.addInt (entryGPR initial 2) (16)) := by
    rw [regionAddress]
    exact SecpCurrentEntry.span (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan mapping base initial
      initialInv.core.v1.current queries X 32 2 (by decide) (by rfl) (by decide)
  have binding : DefaultPairSelected.Binding (view EntryBinding.plan mapping initial) X 2 mapping 2#7 2#5 x := by
    unfold DefaultPairSelected.Binding
    rw [source]
    exact span
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_5 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 2#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 5 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 5 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) ≤ DefaultState.drawsBefore initial (5+1) := by
    rw [cost, DefaultState.budget_next_5]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (5+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 5 + 4#64 = offset EntryBinding.plan (5+1) from by decide)
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_5 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.ldp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 5 (by decide) page (by decide)
    2#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_5 initial)
    statusBound drawBound (room_5 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next X 2 binding
    [((.x 4), none), ((.x 3), none)] (by decide) (by rfl) (by simpa only [word_5] using ob)
#print axioms site_5
#print axioms word_5
#print axioms step_5

theorem site_21 : EntryBinding.plan.code[21]? = some (5772, 2835355653) := rfl
theorem room_21 (initial : NativeState) : 21 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_21 : NativeEntryBodyDispatch.Stp8.selected 5#5 0#5 6#5 0#7 = 2835355653#32 := by decide
theorem step_21 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 21 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (21+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[21]'(room_21 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[4]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_21 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 21 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 21 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.drawsBefore initial (21+1) := by
    rw [cost, DefaultState.budget_next_21]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (21+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 21 + 4#64 = offset EntryBinding.plan (21+1) from by decide)
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_21 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.stp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 21 (by decide) page (by decide)
    0#7 0#5 5#5 6#5 (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_21 initial)
    statusBound drawBound (room_21 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next O 0 binding
    (by decide) (by decide) layout.injective
    [] (by decide) (by rfl) (by simpa only [word_21] using ob)
#print axioms site_21
#print axioms word_21
#print axioms step_21

theorem site_22 : EntryBinding.plan.code[22]? = some (5776, 2835423239) := rfl
theorem room_22 (initial : NativeState) : 22 < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by rw [plan_length_c00]; decide
theorem word_22 : NativeEntryBodyDispatch.Stp8.selected 7#5 0#5 8#5 2#7 = 2835423239#32 := by decide
theorem step_22 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 22 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (22+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[22]'(room_22 initial)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  obtain ⟨entryTopology, entryInv, _, _, _, rams, queries⟩ :=
    DefaultState.initial_from_check raw config rows mapping base initial catalogue checked
  have initialInv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial := entryInv
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[5]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_22 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 22 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have drawBound : DefaultState.drawsBefore initial 22 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.drawsBefore initial (22+1) := by
    rw [cost, DefaultState.budget_next_22]
    exact Nat.le_refl _
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (22+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 22 + 4#64 = offset EntryBinding.plan (22+1) from by decide)
  have compiles : (ValuePlan.compileRun .f regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c00 σ0_c00 (Default.inputs mapping initial).length (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c00 _
  have ob := Default.fetch_22 raw config rows mapping base initial catalogue topology x inv.core layout
  exact DefaultSelectedPairFacts.stp_step real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) EntryBinding.plan.code.length 22 (by decide) page (by decide)
    2#7 0#5 7#5 8#5 (by decide) (by decide) (by decide)
    (view EntryBinding.plan mapping initial) regions_c00 σ0_c00 (Default.inputs mapping initial) .f (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))
    (profile initial) catalogue initial (DefaultState.capacity initial)
    (DefaultState.drawsBefore initial) x inv (DefaultState.budget_room_22 initial)
    statusBound drawBound (room_22 initial) compiles (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (SecpCurrentEntry.table_output EntryBinding.plan raw mapping base initial layout)
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout)
    facts next O 2 binding
    (by decide) (by decide) layout.injective
    [] (by decide) (by rfl) (by simpa only [word_22] using ob)
#print axioms site_22
#print axioms word_22
#print axioms step_22

theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (checked : DefaultState.check raw config rows mapping base initial catalogue = true)
    (k : Nat) (room : k < (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length)
    (selected : k ∈ ([0, 1, 4, 5, 21, 22] : List Nat))
    (x : NativeState) (inv : DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c00 ((plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'room) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_0 real raw config rows mapping base initial catalogue topology layout page checked x inv
  · exact step_1 real raw config rows mapping base initial catalogue topology layout page checked x inv
  · exact step_4 real raw config rows mapping base initial catalogue topology layout page checked x inv
  · exact step_5 real raw config rows mapping base initial catalogue topology layout page checked x inv
  · exact step_21 real raw config rows mapping base initial catalogue topology layout page checked x inv
  · exact step_22 real raw config rows mapping base initial catalogue topology layout page checked x inv
#print axioms all_steps

end PipeLean_D234_SecpAdd_c01.DefaultPairSites
