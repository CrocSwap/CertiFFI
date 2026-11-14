-- GENERATED: complete 18 actual model steps from a current entry invariant; AUX until entry producer/admission.
import PipeSecpSubPlan.CurrentLoads
import PipeSecpSubPlan.CurrentStores
import PipeSecpSubPlan.CurrentArithmetic
import PipeSecpSubPlan.ReturnPC
import ArmCertPipe.FRelease
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open Uget.Chain ArmBridge.CruxGenGuarded ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace ArmCertPipe.F
open CertiFFI.Prog.Generic.ModelRunView
theorem run_of_successful_steps (real : Type) [Sail.SailReal real] (n : Nat) (entry : NativeState)
    (steps : ∀ k, k < n → modelStep real (stateAt real entry k) = .ok () (stateAt real entry (k + 1))) :
    modelRun real n entry = .ok () (stateAt real entry n) := by
  induction n generalizing entry with
  | zero => rfl
  | succ n ih =>
    have first : modelStep real entry = .ok () (next real entry) := by
      simpa only [stateAt] using steps 0 (by omega)
    have rest : ∀ k, k < n → modelStep real (stateAt real (next real entry) k) =
        .ok () (stateAt real (next real entry) (k + 1)) := by
      intro k hk
      simpa only [stateAt_succ_start] using steps (k + 1) (by omega)
    rw [modelRun,first]
    simpa only [stateAt_succ_start] using ih (next real entry) rest
#print axioms run_of_successful_steps
end ArmCertPipe.F
namespace PipeSecpSubPlan
theorem current_run_c05 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c05) (room : 18 ≤ budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (injective : Physical.RegionsInjective view regions_c05)
    (span0 : TranslateSpan.SelectedBinding.At view X 0 mapping (selectedSite_c05 inputs 0).address)
    (ram0 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 0).address = true)
    (span1 : TranslateSpan.SelectedBinding.At view Y 0 mapping (selectedSite_c05 inputs 1).address)
    (ram1 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 1).address = true)
    (span4 : TranslateSpan.SelectedBinding.At view X 2 mapping (selectedSite_c05 inputs 4).address)
    (ram4 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 4).address = true)
    (span5 : TranslateSpan.SelectedBinding.At view Y 2 mapping (selectedSite_c05 inputs 5).address)
    (ram5 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 5).address = true)
    (span15 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c05 inputs 15).address)
    (ram15 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 15).address = true)
    (output15 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (span16 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c05 inputs 16).address)
    (ram16 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 16).address = true)
    (output16 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (lrLow : (inputs.getD (retLRId_c05 tp) 0).toNat < 2 ^ 55)
    (entry : NativeState) (init : CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 0 entry) :
    modelRun real 18 entry = .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    Physical.Agrees view (extend inputs (D_table_c05 tp)) (finalSym_c05 tp)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18).regs._PC = inputs.getD (retLRId_c05 tp) 0 := by
  have step : ∀ k, k < 17 → ∀ x, CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile k x →
      ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile (k + 1) fin := by
    intro k hk x inv
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨fin,run,next,effect⟩ := current_load_c05_0 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span0 ram0 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c05_1 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span1 ram1 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_2 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_3 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c05_4 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span4 ram4 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c05_5 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span5 ram5 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_6 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_7 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_8 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_9 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_10 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_11 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_12 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_13 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c05_14 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c05 inputs base mapping table) (selected_fetch_c05 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c05_15 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span15 ram15 D codeD output15 injective x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c05_16 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span16 ram16 D codeD output16 injective x inv
      exact ⟨fin,run,next⟩
  have reached := ArmCertPipe.F.chainG real (CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile) entry 17 init step
  let last := CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 17
  have lastInv : CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 17 last := reached 17 (Nat.le_refl _)
  have old := legacy_current_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 17 last lastInv
  obtain ⟨fin,run,pc,g,sp,hn,hz,hc,hv,memory,z,tpframe⟩ := ret_exit_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget
    view inputs (last.regs.bank_BitVec_64 .TPIDR_EL0) cs (by omega) page (selectedConsumer_c05 inputs base mapping table)
    (selected_fetch_c05 inputs base mapping table) hlen lrLow last old
  have finalState : CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18 = fin :=
    ArmCertValue.Physical.stateAt_succ_of' run
  have effect : ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 17 (by rw [plan_length_c05]; decide)) last fin :=
    ⟨TranslateStepV.BranchX.vholds_nil g sp hn hz hc hv,Physical.memV_nil_of_mem view regions_c05 last fin memory⟩
  have finalAt := ArmCertPipe.F.agreesAt_succ (by rw [plan_length_c05]; decide)
    (compiles_inputs_c05 inputs tp hlen) lastInv.extra.1 effect
  have compiled : ArmCertValue.F.compileRun regions_c05 σ0_c05 inputs.length (plan_c05 tp) = some (D_table_c05 tp,finalSym_c05 tp) := by
    rw [hlen]; have h := compiles_D_c05 tp; rw [D_table_eq_c05 tp] at h; exact h
  have agrees := ArmCertPipe.F.agrees_end (by simpa only [plan_length_c05] using finalAt) compiled
  have successful : ∀ k, k < 18 → modelStep real (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) =
      .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry (k + 1)) := by
    intro k hk
    by_cases early : k < 17
    · obtain ⟨next,r,nextInv⟩ := step k early _ (reached k (by omega))
      simpa only [ArmCertValue.Physical.stateAt_succ_of' r] using r
    · have equal : k = 17 := by omega
      subst k
      simpa only [finalState] using run
  exact ⟨ArmCertPipe.F.run_of_successful_steps real 18 entry successful,
    by rwa [finalState],by simpa only [finalState,retLRId_c05] using pc⟩
#print axioms current_run_c05

theorem current_run_c06 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c06) (room : 18 ≤ budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (injective : Physical.RegionsInjective view regions_c06)
    (span0 : TranslateSpan.SelectedBinding.At view X 0 mapping (selectedSite_c06 inputs 0).address)
    (ram0 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 0).address = true)
    (span1 : TranslateSpan.SelectedBinding.At view X 0 mapping (selectedSite_c06 inputs 1).address)
    (ram1 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 1).address = true)
    (span4 : TranslateSpan.SelectedBinding.At view X 2 mapping (selectedSite_c06 inputs 4).address)
    (ram4 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 4).address = true)
    (span5 : TranslateSpan.SelectedBinding.At view X 2 mapping (selectedSite_c06 inputs 5).address)
    (ram5 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 5).address = true)
    (span15 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c06 inputs 15).address)
    (ram15 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 15).address = true)
    (output15 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (span16 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c06 inputs 16).address)
    (ram16 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 16).address = true)
    (output16 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (lrLow : (inputs.getD (retLRId_c06 tp) 0).toNat < 2 ^ 55)
    (entry : NativeState) (init : CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 0 entry) :
    modelRun real 18 entry = .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    Physical.Agrees view (extend inputs (D_table_c06 tp)) (finalSym_c06 tp)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18).regs._PC = inputs.getD (retLRId_c06 tp) 0 := by
  have step : ∀ k, k < 17 → ∀ x, CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile k x →
      ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile (k + 1) fin := by
    intro k hk x inv
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨fin,run,next,effect⟩ := current_load_c06_0 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span0 ram0 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c06_1 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span1 ram1 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_2 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_3 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c06_4 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span4 ram4 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c06_5 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span5 ram5 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_6 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_7 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_8 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_9 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_10 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_11 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_12 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_13 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c06_14 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c06 inputs base mapping table) (selected_fetch_c06 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c06_15 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span15 ram15 D codeD output15 injective x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c06_16 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span16 ram16 D codeD output16 injective x inv
      exact ⟨fin,run,next⟩
  have reached := ArmCertPipe.F.chainG real (CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile) entry 17 init step
  let last := CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 17
  have lastInv : CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 17 last := reached 17 (Nat.le_refl _)
  have old := legacy_current_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 17 last lastInv
  obtain ⟨fin,run,pc,g,sp,hn,hz,hc,hv,memory,z,tpframe⟩ := ret_exit_c06 real spec config rows mapping table sc bytes b cb base ifunc p budget
    view inputs (last.regs.bank_BitVec_64 .TPIDR_EL0) cs (by omega) page (selectedConsumer_c06 inputs base mapping table)
    (selected_fetch_c06 inputs base mapping table) hlen lrLow last old
  have finalState : CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18 = fin :=
    ArmCertValue.Physical.stateAt_succ_of' run
  have effect : ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 17 (by rw [plan_length_c06]; decide)) last fin :=
    ⟨TranslateStepV.BranchX.vholds_nil g sp hn hz hc hv,Physical.memV_nil_of_mem view regions_c06 last fin memory⟩
  have finalAt := ArmCertPipe.F.agreesAt_succ (by rw [plan_length_c06]; decide)
    (compiles_inputs_c06 inputs tp hlen) lastInv.extra.1 effect
  have compiled : ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length (plan_c06 tp) = some (D_table_c06 tp,finalSym_c06 tp) := by
    rw [hlen]; have h := compiles_D_c06 tp; rw [D_table_eq_c06 tp] at h; exact h
  have agrees := ArmCertPipe.F.agrees_end (by simpa only [plan_length_c06] using finalAt) compiled
  have successful : ∀ k, k < 18 → modelStep real (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) =
      .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry (k + 1)) := by
    intro k hk
    by_cases early : k < 17
    · obtain ⟨next,r,nextInv⟩ := step k early _ (reached k (by omega))
      simpa only [ArmCertValue.Physical.stateAt_succ_of' r] using r
    · have equal : k = 17 := by omega
      subst k
      simpa only [finalState] using run
  exact ⟨ArmCertPipe.F.run_of_successful_steps real 18 entry successful,
    by rwa [finalState],by simpa only [finalState,retLRId_c06] using pc⟩
#print axioms current_run_c06

theorem current_run_c07 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c07) (room : 18 ≤ budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (injective : Physical.RegionsInjective view regions_c07)
    (span0 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c07 inputs 0).address)
    (ram0 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 0).address = true)
    (span1 : TranslateSpan.SelectedBinding.At view Y 0 mapping (selectedSite_c07 inputs 1).address)
    (ram1 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 1).address = true)
    (span4 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c07 inputs 4).address)
    (ram4 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 4).address = true)
    (span5 : TranslateSpan.SelectedBinding.At view Y 2 mapping (selectedSite_c07 inputs 5).address)
    (ram5 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 5).address = true)
    (span15 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c07 inputs 15).address)
    (ram15 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 15).address = true)
    (output15 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (span16 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c07 inputs 16).address)
    (ram16 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 16).address = true)
    (output16 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (lrLow : (inputs.getD (retLRId_c07 tp) 0).toNat < 2 ^ 55)
    (entry : NativeState) (init : CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 0 entry) :
    modelRun real 18 entry = .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    Physical.Agrees view (extend inputs (D_table_c07 tp)) (finalSym_c07 tp)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18).regs._PC = inputs.getD (retLRId_c07 tp) 0 := by
  have step : ∀ k, k < 17 → ∀ x, CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile k x →
      ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile (k + 1) fin := by
    intro k hk x inv
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨fin,run,next,effect⟩ := current_load_c07_0 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span0 ram0 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c07_1 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span1 ram1 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_2 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_3 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c07_4 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span4 ram4 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c07_5 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span5 ram5 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_6 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_7 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_8 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_9 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_10 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_11 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_12 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_13 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c07_14 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c07 inputs base mapping table) (selected_fetch_c07 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c07_15 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span15 ram15 D codeD output15 injective x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c07_16 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span16 ram16 D codeD output16 injective x inv
      exact ⟨fin,run,next⟩
  have reached := ArmCertPipe.F.chainG real (CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile) entry 17 init step
  let last := CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 17
  have lastInv : CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 17 last := reached 17 (Nat.le_refl _)
  have old := legacy_current_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 17 last lastInv
  obtain ⟨fin,run,pc,g,sp,hn,hz,hc,hv,memory,z,tpframe⟩ := ret_exit_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget
    view inputs (last.regs.bank_BitVec_64 .TPIDR_EL0) cs (by omega) page (selectedConsumer_c07 inputs base mapping table)
    (selected_fetch_c07 inputs base mapping table) hlen lrLow last old
  have finalState : CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18 = fin :=
    ArmCertValue.Physical.stateAt_succ_of' run
  have effect : ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 17 (by rw [plan_length_c07]; decide)) last fin :=
    ⟨TranslateStepV.BranchX.vholds_nil g sp hn hz hc hv,Physical.memV_nil_of_mem view regions_c07 last fin memory⟩
  have finalAt := ArmCertPipe.F.agreesAt_succ (by rw [plan_length_c07]; decide)
    (compiles_inputs_c07 inputs tp hlen) lastInv.extra.1 effect
  have compiled : ArmCertValue.F.compileRun regions_c07 σ0_c07 inputs.length (plan_c07 tp) = some (D_table_c07 tp,finalSym_c07 tp) := by
    rw [hlen]; have h := compiles_D_c07 tp; rw [D_table_eq_c07 tp] at h; exact h
  have agrees := ArmCertPipe.F.agrees_end (by simpa only [plan_length_c07] using finalAt) compiled
  have successful : ∀ k, k < 18 → modelStep real (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) =
      .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry (k + 1)) := by
    intro k hk
    by_cases early : k < 17
    · obtain ⟨next,r,nextInv⟩ := step k early _ (reached k (by omega))
      simpa only [ArmCertValue.Physical.stateAt_succ_of' r] using r
    · have equal : k = 17 := by omega
      subst k
      simpa only [finalState] using run
  exact ⟨ArmCertPipe.F.run_of_successful_steps real 18 entry successful,
    by rwa [finalState],by simpa only [finalState,retLRId_c07] using pc⟩
#print axioms current_run_c07

theorem current_run_c08 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c08) (room : 18 ≤ budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (injective : Physical.RegionsInjective view regions_c08)
    (span0 : TranslateSpan.SelectedBinding.At view X 0 mapping (selectedSite_c08 inputs 0).address)
    (ram0 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 0).address = true)
    (span1 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c08 inputs 1).address)
    (ram1 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 1).address = true)
    (span4 : TranslateSpan.SelectedBinding.At view X 2 mapping (selectedSite_c08 inputs 4).address)
    (ram4 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 4).address = true)
    (span5 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c08 inputs 5).address)
    (ram5 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 5).address = true)
    (span15 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c08 inputs 15).address)
    (ram15 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 15).address = true)
    (output15 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (span16 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c08 inputs 16).address)
    (ram16 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 16).address = true)
    (output16 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (lrLow : (inputs.getD (retLRId_c08 tp) 0).toNat < 2 ^ 55)
    (entry : NativeState) (init : CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 0 entry) :
    modelRun real 18 entry = .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    Physical.Agrees view (extend inputs (D_table_c08 tp)) (finalSym_c08 tp)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18).regs._PC = inputs.getD (retLRId_c08 tp) 0 := by
  have step : ∀ k, k < 17 → ∀ x, CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile k x →
      ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile (k + 1) fin := by
    intro k hk x inv
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨fin,run,next,effect⟩ := current_load_c08_0 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span0 ram0 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c08_1 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span1 ram1 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_2 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_3 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c08_4 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span4 ram4 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c08_5 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span5 ram5 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_6 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_7 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_8 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_9 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_10 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_11 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_12 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_13 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c08_14 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c08 inputs base mapping table) (selected_fetch_c08 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c08_15 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span15 ram15 D codeD output15 injective x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c08_16 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span16 ram16 D codeD output16 injective x inv
      exact ⟨fin,run,next⟩
  have reached := ArmCertPipe.F.chainG real (CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile) entry 17 init step
  let last := CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 17
  have lastInv : CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 17 last := reached 17 (Nat.le_refl _)
  have old := legacy_current_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 17 last lastInv
  obtain ⟨fin,run,pc,g,sp,hn,hz,hc,hv,memory,z,tpframe⟩ := ret_exit_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget
    view inputs (last.regs.bank_BitVec_64 .TPIDR_EL0) cs (by omega) page (selectedConsumer_c08 inputs base mapping table)
    (selected_fetch_c08 inputs base mapping table) hlen lrLow last old
  have finalState : CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18 = fin :=
    ArmCertValue.Physical.stateAt_succ_of' run
  have effect : ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 17 (by rw [plan_length_c08]; decide)) last fin :=
    ⟨TranslateStepV.BranchX.vholds_nil g sp hn hz hc hv,Physical.memV_nil_of_mem view regions_c08 last fin memory⟩
  have finalAt := ArmCertPipe.F.agreesAt_succ (by rw [plan_length_c08]; decide)
    (compiles_inputs_c08 inputs tp hlen) lastInv.extra.1 effect
  have compiled : ArmCertValue.F.compileRun regions_c08 σ0_c08 inputs.length (plan_c08 tp) = some (D_table_c08 tp,finalSym_c08 tp) := by
    rw [hlen]; have h := compiles_D_c08 tp; rw [D_table_eq_c08 tp] at h; exact h
  have agrees := ArmCertPipe.F.agrees_end (by simpa only [plan_length_c08] using finalAt) compiled
  have successful : ∀ k, k < 18 → modelStep real (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) =
      .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry (k + 1)) := by
    intro k hk
    by_cases early : k < 17
    · obtain ⟨next,r,nextInv⟩ := step k early _ (reached k (by omega))
      simpa only [ArmCertValue.Physical.stateAt_succ_of' r] using r
    · have equal : k = 17 := by omega
      subst k
      simpa only [finalState] using run
  exact ⟨ArmCertPipe.F.run_of_successful_steps real 18 entry successful,
    by rwa [finalState],by simpa only [finalState,retLRId_c08] using pc⟩
#print axioms current_run_c08

theorem current_run_c09 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c09) (room : 18 ≤ budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (injective : Physical.RegionsInjective view regions_c09)
    (span0 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c09 inputs 0).address)
    (ram0 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 0).address = true)
    (span1 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c09 inputs 1).address)
    (ram1 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 1).address = true)
    (span4 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c09 inputs 4).address)
    (ram4 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 4).address = true)
    (span5 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c09 inputs 5).address)
    (ram5 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 5).address = true)
    (span15 : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c09 inputs 15).address)
    (ram15 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 15).address = true)
    (output15 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (span16 : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c09 inputs 16).address)
    (ram16 : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 16).address = true)
    (output16 : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (lrLow : (inputs.getD (retLRId_c09 tp) 0).toNat < 2 ^ 55)
    (entry : NativeState) (init : CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 0 entry) :
    modelRun real 18 entry = .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    Physical.Agrees view (extend inputs (D_table_c09 tp)) (finalSym_c09 tp)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18).regs._PC = inputs.getD (retLRId_c09 tp) 0 := by
  have step : ∀ k, k < 17 → ∀ x, CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile k x →
      ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile (k + 1) fin := by
    intro k hk x inv
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨fin,run,next,effect⟩ := current_load_c09_0 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span0 ram0 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c09_1 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span1 ram1 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_2 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_3 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c09_4 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span4 ram4 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_load_c09_5 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span5 ram5 x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_6 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_7 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_8 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_9 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_10 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_11 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_12 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_13 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_arithmetic_c09_14 real spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp cs (by omega) page (selectedConsumer_c09 inputs base mapping table) (selected_fetch_c09 inputs base mapping table) profile hlen x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c09_15 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span15 ram15 D codeD output15 injective x inv
      exact ⟨fin,run,next⟩
    · obtain ⟨fin,run,next,effect⟩ := current_store_c09_16 real domain spec config rows mapping table sc bytes b cb base ifunc p budget
        view inputs tp profile hlen (by omega) page cs (beforeFetchState entry) init.v2.closed span16 ram16 D codeD output16 injective x inv
      exact ⟨fin,run,next⟩
  have reached := ArmCertPipe.F.chainG real (CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile) entry 17 init step
  let last := CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 17
  have lastInv : CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 17 last := reached 17 (Nat.le_refl _)
  have old := legacy_current_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 17 last lastInv
  obtain ⟨fin,run,pc,g,sp,hn,hz,hc,hv,memory,z,tpframe⟩ := ret_exit_c09 real spec config rows mapping table sc bytes b cb base ifunc p budget
    view inputs (last.regs.bank_BitVec_64 .TPIDR_EL0) cs (by omega) page (selectedConsumer_c09 inputs base mapping table)
    (selected_fetch_c09 inputs base mapping table) hlen lrLow last old
  have finalState : CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 18 = fin :=
    ArmCertValue.Physical.stateAt_succ_of' run
  have effect : ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 17 (by rw [plan_length_c09]; decide)) last fin :=
    ⟨TranslateStepV.BranchX.vholds_nil g sp hn hz hc hv,Physical.memV_nil_of_mem view regions_c09 last fin memory⟩
  have finalAt := ArmCertPipe.F.agreesAt_succ (by rw [plan_length_c09]; decide)
    (compiles_inputs_c09 inputs tp hlen) lastInv.extra.1 effect
  have compiled : ArmCertValue.F.compileRun regions_c09 σ0_c09 inputs.length (plan_c09 tp) = some (D_table_c09 tp,finalSym_c09 tp) := by
    rw [hlen]; have h := compiles_D_c09 tp; rw [D_table_eq_c09 tp] at h; exact h
  have agrees := ArmCertPipe.F.agrees_end (by simpa only [plan_length_c09] using finalAt) compiled
  have successful : ∀ k, k < 18 → modelStep real (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) =
      .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry (k + 1)) := by
    intro k hk
    by_cases early : k < 17
    · obtain ⟨next,r,nextInv⟩ := step k early _ (reached k (by omega))
      simpa only [ArmCertValue.Physical.stateAt_succ_of' r] using r
    · have equal : k = 17 := by omega
      subst k
      simpa only [finalState] using run
  exact ⟨ArmCertPipe.F.run_of_successful_steps real 18 entry successful,
    by rwa [finalState],by simpa only [finalState,retLRId_c09] using pc⟩
#print axioms current_run_c09

end PipeSecpSubPlan
