import PipeLean_D234_SecpSub_c07.DitBodyState
import DitShim243.RawFetch
import PipeLean_D234_SecpSub_c07.DefaultState
import PipeLean_D234_SecpSub_c07.CompilerTable
import TranslateSpan.DefaultRet
import ArmCertPipe.FPrefix
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c07.DitBodyTerminal

theorem original_lr (mapping : BitVec 64 → Option Nat) (initial x : NativeState)
    (agreement : ValuePlan.AgreesAt .f (view EntryBinding.plan mapping initial)
      regions_c07 σ0_c07 (Default.inputs mapping initial)
      (plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 17 x) :
    x.regs.gpr[(GPRSummary.key (30#5).toNat).val] = entryGPR initial 30 := by
  let tp := initial.regs.bank_BitVec_64 .TPIDR_EL0
  have whole : F.compileRun regions_c07 σ0_c07 (Default.inputs mapping initial).length
      (plan_c07 tp) = some (D_c07 tp, finalSym_c07 tp) := by
    rw [Default.inputs_length]; exact compiles_D_c07 tp
  have current : (F.compileRun regions_c07 σ0_c07 (Default.inputs mapping initial).length
      ((plan_c07 tp).take 17)).map (fun q => q.2.regs (.x 30)) = some (some lrTableId_c07) := by
    rw [Default.inputs_length]; exact lr_table_c07 tp
  have value := ArmCertPipe.F.regVal_of_agreesAt agreement whole current
  have index : lrTableId_c07 < (Default.inputs mapping initial).length := by
    rw [Default.inputs_length]
    change totalL rs_c07 + 30 < totalL rs_c07 + 36
    omega
  rw [getD_extend_input _ _ index] at value
  have input : (Default.inputs mapping initial).getD lrTableId_c07 0 = entryGPR initial 30 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 30 (by decide)
  change regVal x (.x 30) = entryGPR initial 30
  exact value.trans input

theorem terminal (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0) (low : (entryGPR initial 30).toNat < 2 ^ 55)
    (x : NativeState)
    (inv : DitBodyState.Inv
      (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology)
      raw config rows mapping base initial catalogue 17 x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c07
        (ValuePlan.legacy .f ⟨[],none,[]⟩) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin ∧
      fin.regs._PC = entryGPR initial 30 ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      ValuePlan.AgreesAt .f (view EntryBinding.plan mapping initial) regions_c07 σ0_c07
        (Default.inputs mapping initial) (plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 18 fin := by
  have member : (5852, 0xd65f03c0) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[17]? = some (5852, 0xd65f03c0) from rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 5852 := by
    rw [inv.core.v1.pc]; rfl
  have fetch := DitShim243.RawFetch.fetch
    (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology)
    config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl layout
    (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (5852, 0xd65f03c0) member pc
  obtain ⟨fin,run,effect,frame,ret,delta⟩ := DefaultRet.terminal real
    (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology)
    config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4) 17
    (profile initial) catalogue x inv.core inv.branch (by decide)
    page (by decide) (30#5) (by decide) (by decide) (entryGPR initial 30)
    (original_lr mapping initial x inv.agrees) low
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using fetch)
    .f (view EntryBinding.plan mapping initial) regions_c07
    (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
  have room : 17 < (plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by
    rw [plan_length_c07]; decide
  have compiles : (ValuePlan.compileRun .f regions_c07 σ0_c07 (Default.inputs mapping initial).length
      (plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true := by
    change (F.compileRun regions_c07 σ0_c07 (Default.inputs mapping initial).length
      (plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0))).isSome = true
    rw [Default.inputs_length]; exact compiles_some_c07 _
  have finalAgreement := ValuePlan.advance .f (view EntryBinding.plan mapping initial)
    regions_c07 σ0_c07 (Default.inputs mapping initial)
    (plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 17 x fin room compiles inv.agrees
    (show ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c07
      ((plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[17]'room) x fin from effect)
  exact ⟨fin,run,effect,frame,ret,delta,finalAgreement⟩

#print axioms original_lr
#print axioms terminal
end PipeLean_D234_SecpSub_c07.DitBodyTerminal
