-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import HeapScalarTagCheck.Tails
import DefaultHeapClassStep
import DefaultHeapCode
import HeapV2StepCerts.Residue.ZSeg_11
import HeapV2StepCerts.Residue.Step5Class_08
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap class_step_339"
theorem class_step_339 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 339 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 339 ≤ drawsBefore (339 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 339 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 339 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (339 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (339 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 339 (DefaultHeapClassStep.Effects spec mapping 339) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 339 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_339 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 339 pins table catalogue static 0x78 0xd2800007
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 339 pins table catalogue static 0x78 0xd2800007
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_339 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 339 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_339

#check "CURRENT_DECL heap class_step_340"
theorem class_step_340 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 340 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 340 ≤ drawsBefore (340 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 340 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 340 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (340 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (340 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 340 (DefaultHeapClassStep.Effects spec mapping 340) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 340 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_340 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 340 pins table catalogue static 0x7c 0xd2800008
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 340 pins table catalogue static 0x7c 0xd2800008
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_340 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 340 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_340

#check "CURRENT_DECL heap class_step_341"
theorem class_step_341 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 341 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 341 ≤ drawsBefore (341 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 341 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 341 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (341 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (341 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 341 (DefaultHeapClassStep.Effects spec mapping 341) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 341 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_341 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 341 pins table catalogue static 0x80 0xd2800009
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 341 pins table catalogue static 0x80 0xd2800009
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_341 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 341 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_341

#check "CURRENT_DECL heap class_step_342"
theorem class_step_342 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 342 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 342 ≤ drawsBefore (342 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 342 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 342 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (342 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (342 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 342 (DefaultHeapClassStep.Effects spec mapping 342) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 342 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_342 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 342 pins table catalogue static 0x84 0xd280000a
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 342 pins table catalogue static 0x84 0xd280000a
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_342 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 342 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_342

#check "CURRENT_DECL heap class_step_343"
theorem class_step_343 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 343 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 343 ≤ drawsBefore (343 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 343 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 343 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (343 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (343 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 343 (DefaultHeapClassStep.Effects spec mapping 343) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 343 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_343 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 343 pins table catalogue static 0x88 0xd280000b
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 343 pins table catalogue static 0x88 0xd280000b
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_343 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 343 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_343

#check "CURRENT_DECL heap class_step_344"
theorem class_step_344 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 344 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 344 ≤ drawsBefore (344 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 344 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 344 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (344 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (344 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 344 (DefaultHeapClassStep.Effects spec mapping 344) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 344 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_344 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 344 pins table catalogue static 0x8c 0xd280000c
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 344 pins table catalogue static 0x8c 0xd280000c
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_344 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 344 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_344

#check "CURRENT_DECL heap class_step_345"
theorem class_step_345 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 345 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 345 ≤ drawsBefore (345 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 345 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 345 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (345 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (345 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 345 (DefaultHeapClassStep.Effects spec mapping 345) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 345 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_345 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 345 pins table catalogue static 0x90 0xd280000d
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 345 pins table catalogue static 0x90 0xd280000d
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_345 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 345 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_345

#check "CURRENT_DECL heap class_step_346"
theorem class_step_346 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 346 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 346 ≤ drawsBefore (346 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 346 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 346 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (346 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (346 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 346 (DefaultHeapClassStep.Effects spec mapping 346) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 346 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_346 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 346 pins table catalogue static 0x94 0xd280000e
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 346 pins table catalogue static 0x94 0xd280000e
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_346 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 346 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_346

#check "CURRENT_DECL heap class_step_347"
theorem class_step_347 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 347 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 347 ≤ drawsBefore (347 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 347 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 347 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (347 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (347 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 347 (DefaultHeapClassStep.Effects spec mapping 347) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 347 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_347 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 347 pins table catalogue static 0x98 0xd280000f
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 347 pins table catalogue static 0x98 0xd280000f
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_347 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 347 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_347

#check "CURRENT_DECL heap class_step_348"
theorem class_step_348 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 348 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 348 ≤ drawsBefore (348 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 348 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 348 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (348 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (348 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 348 (DefaultHeapClassStep.Effects spec mapping 348) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 348 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_348 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 348 pins table catalogue static 0x9c 0xd2800010
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 348 pins table catalogue static 0x9c 0xd2800010
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_348 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 348 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_348

#check "CURRENT_DECL heap class_step_349"
theorem class_step_349 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 349 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 349 ≤ drawsBefore (349 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 349 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 349 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (349 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (349 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 349 (DefaultHeapClassStep.Effects spec mapping 349) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 349 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_349 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 349 pins table catalogue static 0xa0 0xd2800011
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 349 pins table catalogue static 0xa0 0xd2800011
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_349 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 349 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_349

#check "CURRENT_DECL heap class_step_350"
theorem class_step_350 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 350 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 350 ≤ drawsBefore (350 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 350 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 350 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (350 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (350 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 350 (DefaultHeapClassStep.Effects spec mapping 350) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 350 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (DefaultHeapClassStep.fromWN (HeapV2StepCerts.TailWE.tailWN_350 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_21
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 350 pins table catalogue static 0xa4 0xf240083f
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 350 pins table catalogue static 0xa4 0xf240083f
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_350 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 350 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_350

#check "CURRENT_DECL heap class_step_356"
theorem class_step_356 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 356 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 356 ≤ drawsBefore (356 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 356 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 356 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (356 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (356 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 356 (DefaultHeapClassStep.Effects spec mapping 356) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 356 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (DefaultHeapClassStep.fromWF (HeapV2StepCerts.TailWE.tailWF_356 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_11
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 356 pins table catalogue static 0xbc 0x910103ff
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 356 pins table catalogue static 0xbc 0x910103ff
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_356 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 356 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_356

end ReleaseProfile.DefaultHeapBranchRows
