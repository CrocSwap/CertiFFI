-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import HeapScalarTagCheck.Tails
import DefaultHeapClassStep
import DefaultHeapCode
import HeapV2StepCerts.Residue.ZSeg_08
import HeapV2StepCerts.Residue.ZSeg_09
import HeapV2StepCerts.Residue.Step5Class_04
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap class_step_255"
theorem class_step_255 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 255 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 255 ≤ drawsBefore (255 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 255 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 255 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (255 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (255 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 255 (DefaultHeapClassStep.Effects spec mapping 255) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 255 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_255 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 255 pins table catalogue static 0x198 0x9bc37c4a
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 255 pins table catalogue static 0x198 0x9bc37c4a
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_255 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 255 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_255

#check "CURRENT_DECL heap class_step_257"
theorem class_step_257 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 257 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 257 ≤ drawsBefore (257 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 257 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 257 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (257 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (257 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 257 (DefaultHeapClassStep.Effects spec mapping 257) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 257 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_257 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 257 pins table catalogue static 0x1a0 0x9b057c4b
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 257 pins table catalogue static 0x1a0 0x9b057c4b
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_257 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 257 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_257

#check "CURRENT_DECL heap class_step_258"
theorem class_step_258 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 258 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 258 ≤ drawsBefore (258 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 258 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 258 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (258 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (258 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 258 (DefaultHeapClassStep.Effects spec mapping 258) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 258 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_258 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 258 pins table catalogue static 0x1a4 0x9bc57c4c
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 258 pins table catalogue static 0x1a4 0x9bc57c4c
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_258 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 258 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_258

#check "CURRENT_DECL heap class_step_259"
theorem class_step_259 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 259 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 259 ≤ drawsBefore (259 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 259 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 259 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (259 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (259 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 259 (DefaultHeapClassStep.Effects spec mapping 259) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 259 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_259 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 259 pins table catalogue static 0x1a8 0x9b047c47
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 259 pins table catalogue static 0x1a8 0x9b047c47
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_259 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 259 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_259

#check "CURRENT_DECL heap class_step_260"
theorem class_step_260 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 260 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 260 ≤ drawsBefore (260 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 260 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 260 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (260 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (260 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 260 (DefaultHeapClassStep.Effects spec mapping 260) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 260 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_260 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 260 pins table catalogue static 0x1ac 0x9bc47c46
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 260 pins table catalogue static 0x1ac 0x9bc47c46
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_260 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 260 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_260

#check "CURRENT_DECL heap class_step_261"
theorem class_step_261 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 261 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 261 ≤ drawsBefore (261 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 261 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 261 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (261 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (261 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 261 (DefaultHeapClassStep.Effects spec mapping 261) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 261 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_261 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_14
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 261 pins table catalogue static 0x1b0 0xab07014a
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 261 pins table catalogue static 0x1b0 0xab07014a
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_261 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 261 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_261

#check "CURRENT_DECL heap class_step_262"
theorem class_step_262 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 262 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 262 ≤ drawsBefore (262 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 262 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 262 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (262 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (262 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 262 (DefaultHeapClassStep.Effects spec mapping 262) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 262 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_262 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 262 pins table catalogue static 0x1b4 0xba06016b
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 262 pins table catalogue static 0x1b4 0xba06016b
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_262 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 262 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_262

#check "CURRENT_DECL heap class_step_263"
theorem class_step_263 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 263 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 263 ≤ drawsBefore (263 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 263 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 263 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (263 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (263 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 263 (DefaultHeapClassStep.Effects spec mapping 263) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 263 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_263 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 263 pins table catalogue static 0x1b8 0x9b047c67
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 263 pins table catalogue static 0x1b8 0x9b047c67
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_263 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 263 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_263

#check "CURRENT_DECL heap class_step_264"
theorem class_step_264 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 264 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 264 ≤ drawsBefore (264 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 264 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 264 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (264 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (264 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 264 (DefaultHeapClassStep.Effects spec mapping 264) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 264 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_264 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 264 pins table catalogue static 0x1bc 0x9bc47c66
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 264 pins table catalogue static 0x1bc 0x9bc47c66
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_264 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 264 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_264

#check "CURRENT_DECL heap class_step_265"
theorem class_step_265 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 265 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 265 ≤ drawsBefore (265 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 265 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 265 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (265 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (265 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 265 (DefaultHeapClassStep.Effects spec mapping 265) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 265 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_265 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_6
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 265 pins table catalogue static 0x1c0 0x9a1f00c6
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 265 pins table catalogue static 0x1c0 0x9a1f00c6
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_265 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 265 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_265

#check "CURRENT_DECL heap class_step_266"
theorem class_step_266 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 266 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 266 ≤ drawsBefore (266 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 266 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 266 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (266 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (266 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 266 (DefaultHeapClassStep.Effects spec mapping 266) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 266 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_266 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_14
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 266 pins table catalogue static 0x1c4 0xab07016b
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 266 pins table catalogue static 0x1c4 0xab07016b
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_266 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 266 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_266

#check "CURRENT_DECL heap class_step_267"
theorem class_step_267 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 267 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 267 ≤ drawsBefore (267 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 267 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 267 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (267 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (267 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 267 (DefaultHeapClassStep.Effects spec mapping 267) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 267 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_267 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 267 pins table catalogue static 0x1c8 0x9b057c8d
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 267 pins table catalogue static 0x1c8 0x9b057c8d
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_267 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 267 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_267

#check "CURRENT_DECL heap class_step_268"
theorem class_step_268 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 268 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 268 ≤ drawsBefore (268 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 268 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 268 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (268 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (268 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 268 (DefaultHeapClassStep.Effects spec mapping 268) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 268 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_268 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 268 pins table catalogue static 0x1cc 0x9bc57c8e
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 268 pins table catalogue static 0x1cc 0x9bc57c8e
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_268 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 268 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_268

#check "CURRENT_DECL heap class_step_269"
theorem class_step_269 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 269 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 269 ≤ drawsBefore (269 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 269 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 269 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (269 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (269 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 269 (DefaultHeapClassStep.Effects spec mapping 269) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 269 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_269 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 269 pins table catalogue static 0x1d0 0xba06018c
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 269 pins table catalogue static 0x1d0 0xba06018c
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_269 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 269 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_269

#check "CURRENT_DECL heap class_step_270"
theorem class_step_270 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 270 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 270 ≤ drawsBefore (270 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 270 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 270 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (270 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (270 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 270 (DefaultHeapClassStep.Effects spec mapping 270) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 270 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_270 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 270 pins table catalogue static 0x1d4 0x9b057c67
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 270 pins table catalogue static 0x1d4 0x9b057c67
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_270 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 270 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_270

#check "CURRENT_DECL heap class_step_271"
theorem class_step_271 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 271 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 271 ≤ drawsBefore (271 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 271 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 271 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (271 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (271 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 271 (DefaultHeapClassStep.Effects spec mapping 271) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 271 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_271 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 271 pins table catalogue static 0x1d8 0x9bc57c66
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 271 pins table catalogue static 0x1d8 0x9bc57c66
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_271 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 271 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_271

#check "CURRENT_DECL heap class_step_272"
theorem class_step_272 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 272 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 272 ≤ drawsBefore (272 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 272 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 272 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (272 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (272 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 272 (DefaultHeapClassStep.Effects spec mapping 272) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 272 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_272 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_6
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 272 pins table catalogue static 0x1dc 0x9a1f00c6
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 272 pins table catalogue static 0x1dc 0x9a1f00c6
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_272 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 272 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_272

#check "CURRENT_DECL heap class_step_273"
theorem class_step_273 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 273 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 273 ≤ drawsBefore (273 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 273 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 273 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (273 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (273 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 273 (DefaultHeapClassStep.Effects spec mapping 273) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 273 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_273 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_14
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 273 pins table catalogue static 0x1e0 0xab07018c
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 273 pins table catalogue static 0x1e0 0xab07018c
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_273 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 273 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_273

#check "CURRENT_DECL heap class_step_274"
theorem class_step_274 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 274 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 274 ≤ drawsBefore (274 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 274 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 274 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (274 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (274 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 274 (DefaultHeapClassStep.Effects spec mapping 274) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 274 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_274 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 274 pins table catalogue static 0x1e4 0xba0601ad
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 274 pins table catalogue static 0x1e4 0xba0601ad
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_274 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 274 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_274

#check "CURRENT_DECL heap class_step_275"
theorem class_step_275 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 275 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 275 ≤ drawsBefore (275 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 275 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 275 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (275 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (275 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 275 (DefaultHeapClassStep.Effects spec mapping 275) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 275 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_275 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_6
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 275 pins table catalogue static 0x1e8 0x9a1f01ce
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 275 pins table catalogue static 0x1e8 0x9a1f01ce
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_275 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 275 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_275

end ReleaseProfile.DefaultHeapBranchRows
