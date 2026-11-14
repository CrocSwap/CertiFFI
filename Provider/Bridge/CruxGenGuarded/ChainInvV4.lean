import Bridge.CruxGenGuarded.ChainInvV3
import HeapV2StepCerts.ValBind
import RtSaved.SlotCore
import RtS2.Link
import RtBl.CallerInv
import Bridge.CruxGenGuarded.ClassNextV4
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.ChainInvV4
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.ChainInvV3 ArmBridge.CruxGenGuarded.ChainInv
open CertiFFI.Prog.Generic.ModelRunView
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! ChainInv v4 = ChainInv v3 ∧ Memory's value/decision binding (P1, ValBind) ∧
saved-LR field (LrField). The two new fields are carried from per-step RELATIONAL facts, so
every step producer exports a `RichStep`: the actual successor plus a relation R x fin
(register effect Holds, value effect VEff, memory frame, STP/LDP payloads as its kind needs).
`step4_of_rich` lifts a rich v3 step to a v4 step given the step's ValBind carry (Memory
carry_k) and LrField carry (carry_class/branch/mem/store/stp11/ldp354), both
stated over R. NormalPath is a PATH hypothesis (the inputs select path 0), not a field. -/

/-- A step that also exports a relation between the state and its actual successor. -/
def RichStep (real : Type) [Sail.SailReal real] (P Q : NativeState → Prop)
    (R : NativeState → NativeState → Prop) : Prop :=
  ∀ x, P x → ∃ fin, modelStep real x = .ok () fin ∧ Q fin ∧ R x fin

theorem RichStep.step {real : Type} [Sail.SailReal real] {P Q : NativeState → Prop}
    {R : NativeState → NativeState → Prop} (h : RichStep real P Q R) : Uget.Chain.Step real P Q := by
  intro x hx
  obtain ⟨fin, run, q, _⟩ := h x hx
  exact ⟨fin, run, q⟩

structure ChainInv4 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (q : HeapV2StepCerts.ValBind.Inputs) (v19 v30 : BitVec 64) (k : Nat) (x : NativeState) : Prop where
  v3 : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x
  valBind : HeapV2StepCerts.ValBind.ValBind q k x
  lr : RtSaved2.LrField p mapping base v19 v30 k x
  residue : RtBl.CallerInv.CallerResidue x

/-- Every rich step's R frames SCR_EL3 (FEAT_GCS absent), which carries the residue. -/
def GcsFrame (s f : NativeState) : Prop :=
  f.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV4.step4_of_rich"
  (← IO.getStderr).flush

theorem step4_of_rich (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (q : HeapV2StepCerts.ValBind.Inputs) (v19 v30 : BitVec 64) (k : Nat)
    (R : NativeState → NativeState → Prop)
    (rich : RichStep real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) R)
    (vcarry : ∀ s f, HeapV2StepCerts.RegBind.RegBind p k s → HeapV2StepCerts.ValBind.ValBind q k s →
      R s f → HeapV2StepCerts.ValBind.ValBind q (k + 1) f)
    (lcarry : ∀ s f, R s f → RtSaved2.LrField p mapping base v19 v30 k s → RtSaved2.LrField p mapping base v19 v30 (k + 1) f)
    (gcs : ∀ s f, R s f → GcsFrame s f) :
    Uget.Chain.Step real
      (ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k)
      (ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 (k + 1)) := by
  intro x inv
  obtain ⟨fin, run, inv3, rel⟩ := rich x inv.v3
  exact ⟨fin, run, ⟨inv3, vcarry x fin inv.v3.regBind inv.valBind rel, lcarry x fin rel inv.lr,
    RtBl.CallerInv.residue_carry (gcs x fin rel) inv.residue⟩⟩

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV4.plan_step4_class"
  (← IO.getStderr).flush

/-- The class R: register effect, value effect, memory frame and SCR_EL3 frame. -/
def ClassR (k : Nat) (s f : NativeState) : Prop :=
  HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f ∧ HeapV2StepCerts.ValBind.VEff k s f ∧
    f.mem = s.mem ∧ GcsFrame s f

/-- A fixed-class (non-memory, non-branch) step as a rich ChainInv v3 step, from its
value-and-effect-carrying tail (`TailW.ClassTailWAt … (upds k) k`). -/
theorem plan_step4_class (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (tail : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      HeapV2StepCerts.TailW.ClassTailWAt real w writes K x (next x) (HeapV2StepCerts.RegBind.upds k) k)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    RichStep real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) (ClassR k) := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, holds, finMem, sys,
      veff, gcs⟩ :=
    ClassNextV4.entry_class_next_v4 real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) (HeapV2StepCerts.RegBind.upds k) k (tail x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    HeapV2StepCerts.RegBind.carry_step hk holds inv.regBind, ?_, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩, holds, veff, finMem, gcs⟩
  · intro e he n hn i hi; rw [finMem]; exact inv.present e he n hn i hi
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV4.path_run4"
  (← IO.getStderr).flush

/-- Composition: ChainInv v4 and E17 TranslationAgrees at every reached state. -/
theorem path_run4 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (agrees : ConsumerMapAgrees spec mapping m)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (q : HeapV2StepCerts.ValBind.Inputs) (v19 v30 : BitVec 64) (len : Nat)
    (steps : ∀ k, k < len → Uget.Chain.Step real
      (ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k)
      (ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 (k + 1)))
    (entry : NativeState)
    (initial : ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 0 entry) :
    ∀ k, k ≤ len →
      ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k (stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m (stateAt real entry k) := by
  have inv := invariant_prefixes real
    (ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30) len steps entry initial
  have e17 := E17Run.e17_along_steps real spec config rows mapping m agrees
    (ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30) len entry steps initial
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.v3.v2.v1.pins, h.v3.v2.v1.features, h.v3.v2.v1.debug,
      h.v3.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.v3.v2.closed)
  exact fun k hk => ⟨inv k hk, e17 k hk⟩

/-- The exit's lrSaved input from the v4 chain at the RET (k = 357), seeded with entry X30. -/
theorem lrSaved_of_v4 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase : MemReloc.Word} {base : BitVec 64}
    {offset : Nat → BitVec 64} {budget : Nat} {p : HeapV2E17.Pins} {q : HeapV2StepCerts.ValBind.Inputs}
    {v19 v30 : BitVec 64} {x : NativeState}
    (h : ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 357 x) :
    x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = v30 :=
  RtSaved2.lrSaved_of_chain h.lr

#print axioms step4_of_rich
#print axioms plan_step4_class
#print axioms path_run4
#print axioms lrSaved_of_v4
end ArmBridge.CruxGenGuarded.ChainInvV4
