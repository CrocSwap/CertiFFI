-- Memory (/, H-P2): the CT2 frame residue along the v4 run. Res = the registers no plan step
-- writes (X18, X20..X29) keep their entry values, and memory outside the plan's STORE bytes keeps its entry bytes.
-- Carried per step from the step's rich relation R (Holds keep + the memory frame), threaded through Core's step lemmas
-- by step5_of_rich / step5_of_at (= step4_of_* plus the Res carry).
import Bridge.CruxGenGuarded.ChainInvV4
import HeapV2StepCerts.Residue.Keep
import RtS3.Link3
import RtSaved.SlotCore
import HeapV2StepCerts.AccShape
import HeapV2StepCerts.ActionTransport
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.BodyMemD
import HeapV2StepCerts.BranchFrame
import HeapV2StepCerts.C3Byte
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.C3Pair
import HeapV2StepCerts.Carry
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.DataBytes
import HeapV2StepCerts.FetchFrames
import HeapV2StepCerts.FlagRoots
import HeapV2StepCerts.FlagTails
import HeapV2StepCerts.MemConfigFrame
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.MemRunD
import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.MemStepsV3
import HeapV2StepCerts.MemStepsV3_00
import HeapV2StepCerts.MemStepsV3_01
import HeapV2StepCerts.MemStepsV3_02
import HeapV2StepCerts.MemStepsV3_03
import HeapV2StepCerts.MemStepsV3_04
import HeapV2StepCerts.MemStepsV3_05
import HeapV2StepCerts.MemTailD
import HeapV2StepCerts.MemTailLdrb
import HeapV2StepCerts.MemTailPair
import HeapV2StepCerts.MemTailStrb
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.RegBind
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.RegBindData
import HeapV2StepCerts.RegRootsB
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.Straight
import HeapV2StepCerts.StraightV2
import HeapV2StepCerts.TailW
import HeapV2StepCerts.ValBind
import HeapV2StepCerts.ValBindCore
import HeapV2StepCerts.ValBindData
import HeapV2StepCerts.ValueTailDef
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.Residue
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.RegBind
open CertiFFI.Prog.Generic.ModelRunView ArmBridge.Boundary ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-- PA bytes of the plan's STORE accesses (the output buffer O via x0 and the stack frame P via SP). -/
def StoreBytes (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (y : Nat) : Prop :=
  ∃ e ∈ HeapV2Plan.symbolicAccesses, e.2.2.2.2 = true ∧ RtSaved.accPA p mapping e y

/-- The residue field. -/
def Res (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (entry x : NativeState) : Prop :=
  (∀ r ∈ frameRegs, regVal x (.x r) = regVal entry (.x r)) ∧
  (∀ a, ¬ StoreBytes p mapping a → x.mem[a]? = entry.mem[a]?)

theorem res_entry (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (entry : NativeState) :
    Res p mapping entry entry := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- The residue invariant with LrField v3: Res plus RtSaved3.LrField at
step k, so X19 at the RET (k = 357) is the entry X19 (RtSaved3.x19_of_chain), without touching ChainInv4. -/
def ResL (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (base v19 v30 : BitVec 64) (entry : NativeState)
    (k : Nat) (x : NativeState) : Prop :=
  Res p mapping entry x ∧ RtSaved3.LrField p mapping base v19 v30 k x

theorem resL_entry (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    ResL p mapping base (entry.regs.gpr[19]) (entry.regs.gpr[30]) entry 0 entry :=
  ⟨res_entry p mapping entry, RtSaved3.field_zero entry⟩

theorem regs_keep {k : Nat} {p mapping} {entry s f : NativeState} (hk : frameKeep k = true)
    (holds : Holds (upds k) s f) (res : Res p mapping entry s) : ∀ r ∈ frameRegs, regVal f (.x r) = regVal entry (.x r) := by
  intro r mem
  have keep : updOf (upds k) (.x r) = .keep := by
    have := List.all_eq_true.1 hk r mem; simpa using this
  have h := holds (.x r)
  rw [keep] at h
  rw [h]; exact res.1 r mem

/-- Non-memory steps (class / branch / BL / RET): memory unchanged. -/
theorem res_eq {k : Nat} {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {entry s f : NativeState}
    (hk : frameKeep k = true) (holds : Holds (upds k) s f) (mem : f.mem = s.mem)
    (res : Res p mapping entry s) : Res p mapping entry f :=
  ⟨regs_keep hk holds res, fun a h => by rw [mem]; exact res.2 a h⟩

/-- Memory steps: writes stay within D ⊆ the store bytes. -/
theorem res_mem {k : Nat} {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {entry s f : NativeState} {D : Nat → Prop}
    (hk : frameKeep k = true) (holds : Holds (upds k) s f)
    (frame : ∃ written : Nat → Prop, WritesOnly written (fun y => s.mem[y]?) (fun y => f.mem[y]?) ∧ ∀ y, written y → D y)
    (sub : ∀ y, D y → StoreBytes p mapping y) (res : Res p mapping entry s) : Res p mapping entry f := by
  refine ⟨regs_keep hk holds res, fun a h => ?_⟩
  obtain ⟨written, wo, inD⟩ := frame
  rw [show f.mem[a]? = s.mem[a]? from wo a (fun w => h (sub a (inD a w)))]
  exact res.2 a h

/-- A load's (empty) or a store's own bytes are store bytes. -/
theorem sub_false {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} : ∀ y, (fun _ => False) y → StoreBytes p mapping y :=
  fun _ h => h.elim
theorem sub_store {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {e : Nat × Nat × Int × Nat × Bool}
    (member : e ∈ HeapV2Plan.symbolicAccesses) (hw : e.2.2.2.2 = true) :
    ∀ y, RtSaved.accPA p mapping e y → StoreBytes p mapping y := fun _ h => ⟨e, member, hw, h⟩

theorem step5_of_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (q : HeapV2StepCerts.ValBind.Inputs) (v19 v30 : BitVec 64) (k : Nat)
    (R : NativeState → NativeState → Prop)
    (at_ : ∀ x, ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k x →
      ∃ fin, modelStep real x = .ok () fin ∧
        ChainInvV3.ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧ R x fin)
    (vcarry : ∀ s f, RegBind p k s → ValBind.ValBind q k s → R s f → ValBind.ValBind q (k + 1) f)
    (lcarry : ∀ s f, R s f → RtSaved2.LrField p mapping base v19 v30 k s → RtSaved2.LrField p mapping base v19 v30 (k + 1) f)
    (gcs : ∀ s f, R s f → GcsFrame s f)
    (entry : NativeState)
    (rcarry : ∀ s f, R s f → ResL p mapping base v19 v30 entry k s → ResL p mapping base v19 v30 entry (k + 1) f) :
    Uget.Chain.Step real
      (fun x => ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k x ∧ ResL p mapping base v19 v30 entry k x)
      (fun x => ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 (k + 1) x ∧
        ResL p mapping base v19 v30 entry (k + 1) x) := by
  intro x ⟨inv, res⟩
  obtain ⟨fin, run, inv3, rel⟩ := at_ x inv
  exact ⟨fin, run, ⟨inv3, vcarry x fin inv.v3.regBind inv.valBind rel, lcarry x fin rel inv.lr,
    RtBl.CallerInv.residue_carry (gcs x fin rel) inv.residue⟩, rcarry x fin rel res⟩

theorem step5_of_rich (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (q : HeapV2StepCerts.ValBind.Inputs) (v19 v30 : BitVec 64) (k : Nat)
    (R : NativeState → NativeState → Prop)
    (rich : RichStep real (ChainInvV3.ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInvV3.ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) R)
    (vcarry : ∀ s f, RegBind p k s → ValBind.ValBind q k s → R s f → ValBind.ValBind q (k + 1) f)
    (lcarry : ∀ s f, R s f → RtSaved2.LrField p mapping base v19 v30 k s → RtSaved2.LrField p mapping base v19 v30 (k + 1) f)
    (gcs : ∀ s f, R s f → GcsFrame s f)
    (entry : NativeState)
    (rcarry : ∀ s f, R s f → ResL p mapping base v19 v30 entry k s → ResL p mapping base v19 v30 entry (k + 1) f) :
    Uget.Chain.Step real
      (fun x => ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k x ∧ ResL p mapping base v19 v30 entry k x)
      (fun x => ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 (k + 1) x ∧
        ResL p mapping base v19 v30 entry (k + 1) x) :=
  step5_of_at real spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k R
    (fun x inv => rich x inv.v3) vcarry lcarry gcs entry rcarry

#print axioms frameKeep_ok
#print axioms res_mem
#print axioms step5_of_rich
end HeapV2StepCerts.Residue
