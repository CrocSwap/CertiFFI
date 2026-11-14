-- Current heap deployment and the initial functional and ABI invariants.
import DefaultHeapResidue
import DefaultHeapBudget
import HeapV2StepCerts.E17General.Base

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open HeapV2StepCerts.E17General (cmap qOf)
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapRun

structure DeploymentPremises {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat) : Prop where
  static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte
  dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows)
  pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0
  codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping)
  sep : RtSaved.SlotSep pins mapping
  mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  agrees : ConsumerMapAgrees spec mapping (cmap spec mapping base pins)
  np : ValBind.NormalPath pins (qOf entry)
  init : DefaultHeapEntryMem.HeapInv spec config rows mapping (cmap spec mapping base pins) codeScope
    (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 0 entry
  nodup : (spec.logicalRows.map (·.logical)).Nodup
  residue : RtBl.CallerInv.CallerResidue entry
  rowsRoom : ∀ k, k < 357 → drawsBefore k + DefaultHeapBudget.costAt k ≤ capacity
  rowsNext : ∀ k, k < 357 → drawsBefore k + DefaultHeapBudget.costAt k ≤ drawsBefore (k + 1)

abbrev RunInv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (x : NativeState) : Prop :=
  DefaultHeapResidue.Inv spec config rows mapping (cmap spec mapping base pins) codeScope
    (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (qOf entry)
    entry.regs.gpr[19] entry.regs.gpr[30] k x ∧
    Residue.ResL pins mapping base entry.regs.gpr[19] entry.regs.gpr[30] entry k x

theorem initial {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {pins : HeapV2E17.Pins} {entry : NativeState} {budget : Nat}
    {catalogue : NativeMteTagCheck.ControlCatalogue} {capacity : Nat} {drawsBefore : Nat → Nat}
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) :
    RunInv spec config rows mapping base pins entry budget 0 catalogue capacity drawsBefore entry :=
  ⟨⟨dp.init, ValBind.initial _, RtSaved2.field_zero _, dp.residue⟩, Residue.resL_entry pins mapping base entry⟩

#print axioms initial
end ReleaseProfile.DefaultHeapRun
