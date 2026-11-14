import PipeLean_D234_SecpSub_c07.DitBodyState
import DitShim243.RawFetch
import PipeLean_D234_SecpSub_c07.DitBodyScalar
import PipeLean_D234_SecpSub_c07.DitBodyPair
import PipeLean_D234_SecpSub_c07.DitBodyTerminal
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c07.DitBodyRun

private theorem frame_refl (D : Nat → Prop) (x : NativeState) : CurrentMTE2.BodyFrame D x x :=
  ⟨fun _ _ => rfl,rfl,rfl⟩

private theorem frame_trans (D : Nat → Prop) (a b c : NativeState)
    (ab : CurrentMTE2.BodyFrame D a b) (bc : CurrentMTE2.BodyFrame D b c) :
    CurrentMTE2.BodyFrame D a c :=
  ⟨fun pa outside => (bc.writes pa outside).trans (ab.writes pa outside),
    bc.z.trans ab.z,bc.tls.trans ab.tls⟩

theorem room (initial : NativeState) (k : Nat) (hk : k < 17) : k < (plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0)).length := by
  rw [plan_length_c07]; omega

theorem all_nonterminal (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (k : Nat) (hk : k < 17) (x : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue (k+1) fin ∧
      ValuePlan.Holds .f (view EntryBinding.plan mapping initial) regions_c07 ((plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0))[k]'(room initial k hk)) x fin ∧
      CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x fin := by
  have partition : ∀ j ∈ List.range 17,
      j ∈ ([0, 1, 4, 5, 15, 16] : List Nat) ∨ j ∈ ([2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14] : List Nat) := by decide
  rcases partition k (List.mem_range.mpr hk) with selected | selected
  · exact DitBodyPair.all_steps real raw config rows mapping base initial topology layout page receipt
      k (room initial k hk) selected x inv
  · exact DitBodyScalar.all_steps real raw config rows mapping base initial topology layout page
      k (room initial k hk) selected x inv

theorem prefix_frames (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    ∀ k, k ≤ 17 → CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
      initial (stateAt real initial k) := by
  have init := receipt.initialInv
  have layout := receipt.layout
  have page := receipt.page
  let I := fun k x => DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x ∧ CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) initial x
  have reached : ∀ k, k ≤ 17 → I k (stateAt real initial k) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨init,frame_refl _ initial⟩
    | succ j ih =>
      intro bound
      have current := ih (by omega)
      obtain ⟨fin,step,next,_,frame⟩ := all_nonterminal real raw config rows mapping base initial topology layout page receipt j (by omega)
        (stateAt real initial j) current.1
      rw [Physical.stateAt_succ_of' step]
      exact ⟨next,frame_trans _ initial _ fin current.2 frame⟩
  exact fun k hk => (reached k hk).2

theorem run (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    ∃ topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true,
      (∀ k, k < 18 → modelStep real (stateAt real initial k) = .ok () (stateAt real initial (k+1))) ∧
      (∀ k, k ≤ 17 → DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k (stateAt real initial k)) ∧
      ∃ fin, modelStep real (stateAt real initial 17) = .ok () fin ∧
        fin = stateAt real initial 18 ∧
        ValuePlan.AgreesAt .f (view EntryBinding.plan mapping initial) regions_c07 σ0_c07 (Default.inputs mapping initial) (plan_c07 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 18 fin ∧
        CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) initial fin ∧ fin.regs._PC = entryGPR initial 30 ∧
        ∃ used, NativeMteTagCheck.ChoiceDelta initial fin used ∧ used ≤ DefaultState.capacity initial := by
  have init := receipt.initialInv
  have layout := receipt.layout
  have page := receipt.page
  have low := receipt.low
  let I := fun k x => DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x ∧ CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) initial x
  have reached : ∀ k, k ≤ 17 → I k (stateAt real initial k) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨init,frame_refl _ initial⟩
    | succ j ih =>
      intro bound
      have current := ih (by omega)
      obtain ⟨fin,step,next,_,frame⟩ := all_nonterminal real raw config rows mapping base initial topology layout page receipt j (by omega)
        (stateAt real initial j) current.1
      rw [Physical.stateAt_succ_of' step]
      exact ⟨next,frame_trans _ initial _ fin current.2 frame⟩
  have last := reached 17 (Nat.le_refl 17)
  obtain ⟨fin,finalStep,_,finalFrame,returned,delta,agreement⟩ := DitBodyTerminal.terminal real raw config rows mapping base initial topology layout page low
    (stateAt real initial 17) last.1
  have finalState : stateAt real initial 18 = fin := Physical.stateAt_succ_of' finalStep
  refine ⟨topology,?_,fun k hk => (reached k hk).1,fin,finalStep,finalState.symm,agreement,
    frame_trans _ initial _ fin last.2 finalFrame,returned,?_⟩
  · intro k hk
    by_cases before : k < 17
    · obtain ⟨next,step,_,_,_⟩ := all_nonterminal real raw config rows mapping base initial topology layout page receipt k before
        (stateAt real initial k) (reached k (by omega)).1
      rw [Physical.stateAt_succ_of' step]; exact step
    · have eq : k = 17 := by omega
      subst k; rw [finalState]; exact finalStep
  · obtain ⟨used,previous,bound⟩ := last.1.trace
    have budget : DefaultState.drawsBefore initial 17 = DefaultState.capacity initial := by rfl
    refine ⟨used,?_,?_⟩
    · simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans previous delta
    · rw [← budget]; exact bound

#print axioms all_nonterminal
#print axioms prefix_frames
#print axioms run
end PipeLean_D234_SecpSub_c07.DitBodyRun
