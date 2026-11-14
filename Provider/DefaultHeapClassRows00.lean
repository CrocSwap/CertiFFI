-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import HeapScalarTagCheck.Tails
import DefaultHeapClassStep
import DefaultHeapCode
import HeapV2StepCerts.Residue.ZSeg_00
import HeapV2StepCerts.Residue.ZSeg_01
import HeapV2StepCerts.Residue.ZSeg_02
import HeapV2StepCerts.Residue.Step5Class_00
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap class_step_2"
theorem class_step_2 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 2 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 2 ≤ drawsBefore (2 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 2 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 2 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (2 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (2 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 2 (DefaultHeapClassStep.Effects spec mapping 2) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 2 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_2 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_21
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 2 pins table catalogue static 0x8 0xf240081f
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 2 pins table catalogue static 0x8 0xf240081f
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_2 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 2 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_2

#check "CURRENT_DECL heap class_step_4"
theorem class_step_4 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 4 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 4 ≤ drawsBefore (4 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 4 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 4 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (4 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (4 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 4 (DefaultHeapClassStep.Effects spec mapping 4) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 4 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_4 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_21
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 4 pins table catalogue static 0x10 0xf240083f
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 4 pins table catalogue static 0x10 0xf240083f
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_4 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 4 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_4

#check "CURRENT_DECL heap class_step_6"
theorem class_step_6 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 6 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 6 ≤ drawsBefore (6 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 6 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 6 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (6 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (6 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 6 (DefaultHeapClassStep.Effects spec mapping 6) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 6 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_6 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_20
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 6 pins table catalogue static 0x18 0xf100805f
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 6 pins table catalogue static 0x18 0xf100805f
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_6 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 6 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_6

#check "CURRENT_DECL heap class_step_8"
theorem class_step_8 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 8 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 8 ≤ drawsBefore (8 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 8 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 8 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (8 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (8 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 8 (DefaultHeapClassStep.Effects spec mapping 8) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 8 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_8 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_20
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 8 pins table catalogue static 0x20 0xf100807f
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 8 pins table catalogue static 0x20 0xf100807f
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_8 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 8 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_8

#check "CURRENT_DECL heap class_step_10"
theorem class_step_10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 10 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 10 ≤ drawsBefore (10 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 10 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 10 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (10 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (10 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 10 (DefaultHeapClassStep.Effects spec mapping 10) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 10 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_10 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_22
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 10 pins table catalogue static 0x28 0xd10103ff
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 10 pins table catalogue static 0x28 0xd10103ff
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_10 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 10 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_10

#check "CURRENT_DECL heap class_step_12"
theorem class_step_12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 12 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 12 ≤ drawsBefore (12 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 12 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 12 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (12 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (12 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 12 (DefaultHeapClassStep.Effects spec mapping 12) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 12 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_12 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_9
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 12 pins table catalogue static 0x30 0xaa0003f3
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 12 pins table catalogue static 0x30 0xaa0003f3
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_12 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 12 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_12

#check "CURRENT_DECL heap class_step_13"
theorem class_step_13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 13 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 13 ≤ drawsBefore (13 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 13 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 13 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (13 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (13 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 13 (DefaultHeapClassStep.Effects spec mapping 13) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 13 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_13 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_10
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 13 pins table catalogue static 0x34 0x910003e0
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 13 pins table catalogue static 0x34 0x910003e0
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_13 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 13 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_13

#check "CURRENT_DECL heap class_step_14"
theorem class_step_14 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 14 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 14 ≤ drawsBefore (14 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 14 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 14 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (14 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (14 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 14 (DefaultHeapClassStep.Effects spec mapping 14) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 14 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_14 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_2
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 14 pins table catalogue static 0x38 0xd2800402
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 14 pins table catalogue static 0x38 0xd2800402
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_14 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 14 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_14

#check "CURRENT_DECL heap class_step_17"
theorem class_step_17 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 17 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 17 ≤ drawsBefore (17 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 17 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 17 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (17 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (17 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 17 (DefaultHeapClassStep.Effects spec mapping 17) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 17 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_17 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_9
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 17 pins table catalogue static 0x12c 0xaa0003e3
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 17 pins table catalogue static 0x12c 0xaa0003e3
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_17 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 17 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_17

#check "CURRENT_DECL heap class_step_20"
theorem class_step_20 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 20 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 20 ≤ drawsBefore (20 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 20 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 20 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (20 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (20 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 20 (DefaultHeapClassStep.Effects spec mapping 20) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 20 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_20 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 20 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 20 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_20 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 20 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_20

#check "CURRENT_DECL heap class_step_24"
theorem class_step_24 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 24 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 24 ≤ drawsBefore (24 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 24 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 24 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (24 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (24 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 24 (DefaultHeapClassStep.Effects spec mapping 24) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 24 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_24 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 24 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 24 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_24 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 24 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_24

#check "CURRENT_DECL heap class_step_28"
theorem class_step_28 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 28 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 28 ≤ drawsBefore (28 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 28 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 28 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (28 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (28 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 28 (DefaultHeapClassStep.Effects spec mapping 28) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 28 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_28 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 28 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 28 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_28 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 28 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_28

#check "CURRENT_DECL heap class_step_32"
theorem class_step_32 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 32 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 32 ≤ drawsBefore (32 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 32 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 32 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (32 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (32 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 32 (DefaultHeapClassStep.Effects spec mapping 32) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 32 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_32 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 32 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 32 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_32 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 32 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_32

#check "CURRENT_DECL heap class_step_36"
theorem class_step_36 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 36 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 36 ≤ drawsBefore (36 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 36 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 36 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (36 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (36 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 36 (DefaultHeapClassStep.Effects spec mapping 36) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 36 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_36 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 36 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 36 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_36 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 36 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_36

#check "CURRENT_DECL heap class_step_40"
theorem class_step_40 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 40 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 40 ≤ drawsBefore (40 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 40 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 40 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (40 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (40 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 40 (DefaultHeapClassStep.Effects spec mapping 40) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 40 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_40 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 40 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 40 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_40 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 40 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_40

#check "CURRENT_DECL heap class_step_44"
theorem class_step_44 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 44 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 44 ≤ drawsBefore (44 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 44 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 44 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (44 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (44 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 44 (DefaultHeapClassStep.Effects spec mapping 44) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 44 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_44 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 44 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 44 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_44 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 44 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_44

#check "CURRENT_DECL heap class_step_48"
theorem class_step_48 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 48 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 48 ≤ drawsBefore (48 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 48 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 48 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (48 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (48 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 48 (DefaultHeapClassStep.Effects spec mapping 48) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 48 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_48 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 48 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 48 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_48 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 48 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_48

#check "CURRENT_DECL heap class_step_52"
theorem class_step_52 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 52 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 52 ≤ drawsBefore (52 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 52 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 52 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (52 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (52 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 52 (DefaultHeapClassStep.Effects spec mapping 52) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 52 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_52 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 52 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 52 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_52 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 52 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_52

#check "CURRENT_DECL heap class_step_56"
theorem class_step_56 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 56 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 56 ≤ drawsBefore (56 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 56 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 56 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (56 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (56 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 56 (DefaultHeapClassStep.Effects spec mapping 56) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 56 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_56 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 56 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 56 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_56 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 56 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_56

#check "CURRENT_DECL heap class_step_60"
theorem class_step_60 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 60 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 60 ≤ drawsBefore (60 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 60 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 60 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (60 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (60 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 60 (DefaultHeapClassStep.Effects spec mapping 60) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 60 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_60 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 60 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 60 pins table catalogue static 0x138 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_60 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 60 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_60

end ReleaseProfile.DefaultHeapBranchRows
