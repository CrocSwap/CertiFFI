-- d204 SIMD frame: the vector register file _Z (v0..v31, incl. the AAPCS64 callee-saved v8..v15 low halves) is
-- unchanged along a program run when every step keeps it (ZOb k). Per-step ZOb comes from the route lemmas' _Z
-- variants (class: class_vholdsGZ over ClassNextX.entry_class_next_XZ; branch / RET / memory from the owners' tails).
import ArmCertPipe.Dispatch
import TranslateStepV.ClassNextXZ
import TranslateStepV.BranchXZ
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
namespace ArmCertPipe
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView

/-- Step k keeps the vector registers. -/
abbrev ZOb (real : Type) [Sail.SailReal real] (Inv : Nat → NativeState → Prop) (k : Nat) : Prop :=
  ∀ x, Inv k x → ∀ fin, modelStep real x = .ok () fin → fin.regs._Z = x.regs._Z

/-- A route with the _Z frame gives ZOb (determinism of modelStep). -/
theorem zob_of_route {real : Type} [Sail.SailReal real] {Inv : Nat → NativeState → Prop} {k : Nat}
    (r : ∀ x, Inv k x → ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z) : ZOb real Inv k := by
  intro x inv fin run
  obtain ⟨fin', run', z⟩ := r x inv
  rw [run] at run'; cases run'; exact z

/-- **SIMD frame along the run**: the invariant at every step, a successful step from each, and ZOb at every step
    give: the state after the last step has the entry's _Z. -/
theorem zframe_run (real : Type) [Sail.SailReal real] (Inv : Nat → NativeState → Prop) (entry : NativeState)
    (N : Nat) (hne : 0 < N) (inv : ∀ k, k < N → Inv k (stateAt real entry k))
    (step : ∀ k, k < N → ∃ fin, modelStep real (stateAt real entry k) = .ok () fin)
    (z : ∀ k, k < N → ZOb real Inv k) :
    ∀ fin, modelStep real (stateAt real entry (N - 1)) = .ok () fin → fin.regs._Z = entry.regs._Z := by
  have along : ∀ k, k < N → (stateAt real entry k).regs._Z = entry.regs._Z := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      obtain ⟨f, run⟩ := step j (by omega)
      rw [stateAt_succ_of' run, z j (by omega) _ (inv j (by omega)) f run]
      exact ih (by omega)
  intro fin run
  rw [z (N - 1) (by omega) _ (inv (N - 1) (by omega)) fin run]
  exact along (N - 1) (by omega)

/-- class_vholdsG plus the _Z frame. -/
theorem class_vholdsGZ (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (next : NativeState → BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (fl : Option (ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd))
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : ArmCertValue.ClassTailXAt real w writes K x (next x) vus fl)
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, _, _, z⟩ := ArmBridge.CruxGenGuarded.ClassNextX.entry_class_next_XZ real spec config rows mapping
    w writes K x inv.v2.v1.pins (next x) (offset (k + 1)) vus fl tail inv.v2.v1.gic inv.v2.v1.features
    inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
    inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
    inv.raw inv.noUpd obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio obligations.present
    obligations.perAcc obligations.code
  exact ⟨fin, run, z⟩

/-- branch_vholdsG plus the _Z frame (tail: BranchTailNZZ). -/
theorem branch_vholdsGZ (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : TranslateStepV.BranchX.BranchTailNZZ real w K x (next x))
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, z⟩ :=
    TranslateStepV.BranchX.entry_branch_next_XZ real spec config rows mapping w K x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio
      obligations.present obligations.perAcc obligations.code
  exact ⟨fin, run, z⟩

#print axioms branch_vholdsGZ
#print axioms zob_of_route
#print axioms zframe_run
#print axioms class_vholdsGZ
end ArmCertPipe
