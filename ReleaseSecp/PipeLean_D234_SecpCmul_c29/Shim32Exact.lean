import PipeLean_D234_SecpCmul_c29.Shim32Run
import DitShim243.EpiABI
import DitShim243.PreABI
import PipeLean_D234_SecpCmul_c29.DitBodyState
import DitShim243.BodyEntry
import DitShim243.Prologue
import TranslateSpan.DefaultFiniteRows
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts NativeMteTagCheck ReleaseProfile ArmCertValue ArmCertPipe
open CertiFFI.Prog.Generic.ModelRunView DitShim243
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpCmul_c29.Shim32Exact

theorem code_binding : Deployment.shimCode 8444 (67108724#26) =
    [(8444,0xd503245f),(8448,0xd10043ff),(8452,0xd53b42a9),(8456,0xa9007be9),(8460,0xd503415f),(8464,0xd5033fdf),(8468,0x97ffff74),(8472,0xa9407be9),(8476,0x910043ff),(8480,0xd51b42a9),(8484,0xd65f03c0)] := by decide

def check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Bool :=
  InitialCheck.check EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0))
    8444 (67108724#26) 30 pins (DefaultState.capacity entry+2) entry catalogue

theorem run (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)

    (checked : check raw config rows mapping base pins entry catalogue = true) :
    (∀ k, k < 42 → modelStep real (stateAt real entry k) = .ok () (stateAt real entry (k+1))) ∧
    (stateAt real entry 42).regs._PC = entryGPR entry 30 ∧
    (stateAt real entry 42).regs.gpr[30] = entry.regs.gpr[30] ∧
    (stateAt real entry 42).regs.SP_EL0 = entry.regs.SP_EL0 ∧
    (stateAt real entry 42).regs.PSTATE.DIT = entry.regs.PSTATE.DIT ∧
    (∀ j, 5 ≤ j → j ≤ 40 → (stateAt real entry j).regs.PSTATE.DIT = 1#1) ∧
    (∀ pa, pa ∉ outputBytes EntryBinding.plan mapping entry → ¬ RtShim2.ShimMem.slotBytes pins mapping pa →
      (stateAt real entry 42).mem[pa]? = entry.mem[pa]?) ∧
    (∃ used, ChoiceDelta entry (stateAt real entry 42) used ∧ used ≤ DefaultState.capacity entry+2) ∧
    ShimABI.Fields entry (stateAt real entry 42) ∧
    (∀ i : Fin 31, 18 ≤ i.val → (stateAt real entry 42).regs.gpr[i.val] = entry.regs.gpr[i.val]) ∧
    (∀ pa : Nat, (stateAt real entry 42).mem[pa]? = (stateAt real entry 38).mem[pa]?) ∧
    (∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 → (stateAt real entry 7).regs.gpr[i.val] = entry.regs.gpr[i.val]) ∧
    ArmCertMemPipe.TLSFrame.tp (stateAt real entry 7) = ArmCertMemPipe.TLSFrame.tp entry :=
  Shim32Run.run real raw config rows mapping base 8444 (67108724#26) pins entry catalogue checked

theorem same_state_call (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)

    (checked : check raw config rows mapping base pins entry catalogue = true) :
    ∃ topology : CheckedTopology.check raw (addresses EntryBinding.plan base (stateAt real entry 7)) 4 = true,
      DitBodyState.Receipt raw config rows mapping base (stateAt real entry 7) catalogue topology ∧
      (∀ k, k < 31 → modelStep real (stateAt real entry (7+k)) = .ok () (stateAt real entry (7+k+1))) ∧
      ValuePlan.AgreesAt .f (view EntryBinding.plan mapping (stateAt real entry 7)) regions_c00 σ0_c00
        (Default.inputs mapping (stateAt real entry 7)) (plan_c00 ((stateAt real entry 7).regs.bank_BitVec_64 .TPIDR_EL0)) 31 (stateAt real entry 38) ∧
      (∀ r n, (r,n) ∈ EntryBinding.plan.buffers → ∀ i < n,
        Physical.regionByte (view EntryBinding.plan mapping (stateAt real entry 7)) (stateAt real entry 7) r i =
          Physical.regionByte (view EntryBinding.plan mapping entry) entry r i) := by
  obtain ⟨gt,rt,conditions⟩ := InitialCheck.of_check EntryBinding.plan raw config rows mapping base _ 8444 (67108724#26) 30 pins (DefaultState.capacity entry+2) entry catalogue checked
  have info := Initial.of_conditions EntryBinding.plan raw config rows mapping base _ 8444 (67108724#26) 30 pins (DefaultState.capacity entry+2) entry catalogue gt rt conditions
  obtain ⟨pre,_⟩ := Prologue.of_initial real EntryBinding.plan raw config rows mapping base _ 8444 (67108724#26) 30 pins (DefaultState.capacity entry+2) entry catalogue gt rt info
  obtain ⟨topology,receipt⟩ := DitBodyEntry.of_pre real raw config rows mapping base 8444 (67108724#26) pins entry catalogue gt rt info pre
  obtain ⟨_,steps,-,fin,-,finEq,ssa,-⟩ := DitBodyRun.run real raw config rows mapping base (stateAt real entry 7) topology receipt
  rw [finEq,← StateShift.stateAt_add real entry 7 31] at ssa
  have agree := DataTransport.of_pre real 30 _ config rows mapping pins _ 8444 _ _ base base _ 42 _ (DefaultState.capacity entry+2) entry pre EntryBinding.plan (by decide)
  refine ⟨topology,receipt,?_,ssa,?_⟩
  · intro k hk
    simpa only [StateShift.stateAt_add,show 7+k+1=7+(k+1) by omega] using steps k hk
  · intro r n member i bound
    unfold Physical.regionByte
    rw [DataTransport.view agree r (DataFrame.buffer_member EntryBinding.plan r n member) i]
    cases mapped : view EntryBinding.plan mapping entry r i with
    | none => rfl
    | some pa =>
      simp only [Option.bind_some]
      exact pre.memPre pa (info.slotRegions r n (List.mem_append_left _ member) i bound pa mapped)

#print axioms same_state_call

#print axioms code_binding
#print axioms run
end PipeLean_D234_SecpCmul_c29.Shim32Exact
