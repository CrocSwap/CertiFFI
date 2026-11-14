-- d199 program pipeline: the program-generic chain invariant every step route targets.
-- ChainInvG = ChainInv2 (already generic: spec, config, rows, mapping, consumer map, code scope/image, base, offsets,
-- budget) + the program-independent fields of ChainInv3 + a per-program `extra` (heap-v2: register binding to its pins
-- and data presence). Route lemmas are stated once over ChainInvG; a program's E17 chain supplies ChainInvG at each k.
import Bridge.CruxGenGuarded.ChainInvV3
import TranslateStepV.BranchX
import TranslateStepV.BlNZ
import TranslateStepV.ClassNextX
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace ArmCertPipe
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3 HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false

/-- The program-generic chain invariant at step k. -/
structure ChainInvG {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop)
    (k : Nat) (x : NativeState) : Prop where
  v2 : ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x
  raw : RawImageAt spec.imageRows x.mem
  noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
    NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true
  post2 : MemM1.MemReadD2.PostRegs2 x.regs
  mode : HostEL0ModeAt x.regs
  debug : ExistingE11DebugAt x.regs
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  dcache : currentDCache x.regs = true
  extra : extra k x

/-- heap-v2's extra: the register binding to its pins and data-byte presence. -/
def heapV2Extra (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (k : Nat) (x : NativeState) : Prop :=
  HeapV2StepCerts.RegBind.RegBind p k x ∧ HeapV2StepCerts.C3.DataPresent p mapping x

/-- heap-v2's ChainInv3 is ChainInvG with heapV2Extra. -/
theorem ChainInvG.of_v3 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop} {image : MemReloc.Image}
    {loadBase : MemReloc.Word} {base : BitVec 64} {offset : Nat → BitVec 64} {budget : Nat}
    {p : HeapV2E17.Pins} {k : Nat} {x : NativeState}
    (h : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x) :
    ChainInvG spec config rows mapping m scope image loadBase base offset budget (heapV2Extra p mapping) k x :=
  ⟨h.v2, h.raw, h.noUpd, h.post2, h.mode, h.debug, h.feat, h.dcache, ⟨h.regBind, h.present⟩⟩

/-! ## Route statement shape (the generator's per-step obligation before StepFact packaging)
A route for step k with plan entry ⟨us, fl, []⟩ proves, at every x with ChainInvG … k x:
  ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds us fl x fin ∧ fin.mem = x.mem
(memory routes replace `fin.mem = x.mem` with their MemVHolds). Worked examples: the branch and BL routes. -/

/-- A branch step (plan entry ⟨[], none, []⟩) over ChainInvG: any branch tail with NZCV (BranchX.BranchTailNZ). -/
theorem branch_vholdsG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : TranslateStepV.BranchX.BranchTailNZ real w K x (next x))
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, g, sp, n, z, c, v, mem⟩ :=
    TranslateStepV.BranchX.entry_branch_next_X real spec config rows mapping w K x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio
      obligations.present obligations.perAcc obligations.code
  exact ⟨fin, run, TranslateStepV.BranchX.vholds_nil g sp n z c v, mem⟩

/-- A BL step (plan entry ⟨[(.x 30, none)], none, []⟩) over ChainInvG. -/
theorem bl_vholdsG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm26 : BitVec 26)
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (controls : CallerControls x) (tail : TranslateStepV.BlNZ.BlTailNZ real imm26 x)
    (obligations : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [(.x 30, none)] none x fin ∧ fin.mem = x.mem := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, g, sp, n, z, c, v, mem⟩ :=
    TranslateStepV.BlNZ.entry_bl_next_X real spec config rows mapping imm26 x inv.v2.v1.pins tail controls inv.v2.v1.gic
      inv.v2.v1.features inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated
      inv.raw inv.noUpd obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio
      obligations.present obligations.perAcc obligations.code
  exact ⟨fin, run, TranslateStepV.BlNZ.vholds_bl _ g sp n z c v, mem⟩

/-- A class step (plan entry ⟨vus, fl, []⟩) over ChainInvG: value tail (ClassTailXAt). -/
theorem class_vholdsG (real : Type) [Sail.SailReal real]
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
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds vus fl x fin ∧ fin.mem = x.mem := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  exact ArmBridge.CruxGenGuarded.ClassNextX.entry_class_next_X real spec config rows mapping w writes K x
    inv.v2.v1.pins (next x) (offset (k + 1)) vus fl tail inv.v2.v1.gic inv.v2.v1.features
    inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
    inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
    inv.raw inv.noUpd obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio obligations.present
    obligations.perAcc obligations.code

#print axioms class_vholdsG
#print axioms ChainInvG.of_v3
#print axioms branch_vholdsG
#print axioms bl_vholdsG
end ArmCertPipe
