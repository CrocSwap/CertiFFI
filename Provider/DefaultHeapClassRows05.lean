-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import HeapScalarTagCheck.Tails
import DefaultHeapClassStep
import DefaultHeapCode
import HeapV2StepCerts.Residue.ZSeg_09
import HeapV2StepCerts.Residue.Step5Class_05
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap class_step_276"
theorem class_step_276 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 276 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 276 ≤ drawsBefore (276 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 276 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 276 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (276 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (276 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 276 (DefaultHeapClassStep.Effects spec mapping 276) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 276 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_276 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_14
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 276 pins table catalogue static 0x1ec 0xab090129
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 276 pins table catalogue static 0x1ec 0xab090129
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_276 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 276 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_276

#check "CURRENT_DECL heap class_step_277"
theorem class_step_277 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 277 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 277 ≤ drawsBefore (277 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 277 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 277 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (277 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (277 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 277 (DefaultHeapClassStep.Effects spec mapping 277) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 277 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_277 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 277 pins table catalogue static 0x1f0 0xba0a014a
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 277 pins table catalogue static 0x1f0 0xba0a014a
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_277 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 277 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_277

#check "CURRENT_DECL heap class_step_278"
theorem class_step_278 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 278 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 278 ≤ drawsBefore (278 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 278 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 278 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (278 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (278 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 278 (DefaultHeapClassStep.Effects spec mapping 278) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 278 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_278 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 278 pins table catalogue static 0x1f4 0xba0b016b
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 278 pins table catalogue static 0x1f4 0xba0b016b
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_278 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 278 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_278

#check "CURRENT_DECL heap class_step_279"
theorem class_step_279 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 279 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 279 ≤ drawsBefore (279 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 279 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 279 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (279 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (279 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 279 (DefaultHeapClassStep.Effects spec mapping 279) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 279 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_279 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 279 pins table catalogue static 0x1f8 0xba0c018c
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 279 pins table catalogue static 0x1f8 0xba0c018c
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_279 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 279 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_279

#check "CURRENT_DECL heap class_step_280"
theorem class_step_280 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 280 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 280 ≤ drawsBefore (280 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 280 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 280 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (280 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (280 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 280 (DefaultHeapClassStep.Effects spec mapping 280) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 280 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_280 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 280 pins table catalogue static 0x1fc 0xba0d01ad
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 280 pins table catalogue static 0x1fc 0xba0d01ad
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_280 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 280 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_280

#check "CURRENT_DECL heap class_step_281"
theorem class_step_281 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 281 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 281 ≤ drawsBefore (281 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 281 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 281 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (281 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (281 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 281 (DefaultHeapClassStep.Effects spec mapping 281) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 281 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_281 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 281 pins table catalogue static 0x200 0xba0e01ce
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 281 pins table catalogue static 0x200 0xba0e01ce
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_281 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 281 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_281

#check "CURRENT_DECL heap class_step_282"
theorem class_step_282 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 282 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 282 ≤ drawsBefore (282 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 282 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 282 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (282 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (282 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 282 (DefaultHeapClassStep.Effects spec mapping 282) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 282 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_282 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_17
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 282 pins table catalogue static 0x204 0x9a9f37e6
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 282 pins table catalogue static 0x204 0x9a9f37e6
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_282 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 282 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_282

#check "CURRENT_DECL heap class_step_283"
theorem class_step_283 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 283 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 283 ≤ drawsBefore (283 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 283 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 283 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (283 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (283 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 283 (DefaultHeapClassStep.Effects spec mapping 283) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 283 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_283 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 283 pins table catalogue static 0x208 0x9bc27c47
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 283 pins table catalogue static 0x208 0x9bc27c47
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_283 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 283 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_283

#check "CURRENT_DECL heap class_step_284"
theorem class_step_284 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 284 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 284 ≤ drawsBefore (284 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 284 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 284 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (284 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (284 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 284 (DefaultHeapClassStep.Effects spec mapping 284) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 284 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_284 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 284 pins table catalogue static 0x20c 0x9b027c48
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 284 pins table catalogue static 0x20c 0x9b027c48
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_284 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 284 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_284

#check "CURRENT_DECL heap class_step_285"
theorem class_step_285 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 285 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 285 ≤ drawsBefore (285 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 285 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 285 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (285 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (285 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 285 (DefaultHeapClassStep.Effects spec mapping 285) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 285 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_285 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_14
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 285 pins table catalogue static 0x210 0xab070129
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 285 pins table catalogue static 0x210 0xab070129
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_285 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 285 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_285

#check "CURRENT_DECL heap class_step_286"
theorem class_step_286 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 286 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 286 ≤ drawsBefore (286 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 286 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 286 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (286 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (286 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 286 (DefaultHeapClassStep.Effects spec mapping 286) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 286 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_286 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 286 pins table catalogue static 0x214 0x9b037c67
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 286 pins table catalogue static 0x214 0x9b037c67
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_286 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 286 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_286

#check "CURRENT_DECL heap class_step_287"
theorem class_step_287 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 287 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 287 ≤ drawsBefore (287 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 287 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 287 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (287 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (287 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 287 (DefaultHeapClassStep.Effects spec mapping 287) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 287 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_287 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 287 pins table catalogue static 0x218 0xba07014a
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 287 pins table catalogue static 0x218 0xba07014a
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_287 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 287 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_287

#check "CURRENT_DECL heap class_step_288"
theorem class_step_288 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 288 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 288 ≤ drawsBefore (288 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 288 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 288 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (288 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (288 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 288 (DefaultHeapClassStep.Effects spec mapping 288) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 288 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_288 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 288 pins table catalogue static 0x21c 0x9bc37c67
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 288 pins table catalogue static 0x21c 0x9bc37c67
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_288 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 288 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_288

#check "CURRENT_DECL heap class_step_289"
theorem class_step_289 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 289 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 289 ≤ drawsBefore (289 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 289 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 289 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (289 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (289 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 289 (DefaultHeapClassStep.Effects spec mapping 289) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 289 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_289 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 289 pins table catalogue static 0x220 0xba07016b
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 289 pins table catalogue static 0x220 0xba07016b
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_289 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 289 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_289

#check "CURRENT_DECL heap class_step_290"
theorem class_step_290 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 290 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 290 ≤ drawsBefore (290 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 290 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 290 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (290 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (290 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 290 (DefaultHeapClassStep.Effects spec mapping 290) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 290 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_290 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 290 pins table catalogue static 0x224 0x9b047c87
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 290 pins table catalogue static 0x224 0x9b047c87
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_290 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 290 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_290

#check "CURRENT_DECL heap class_step_291"
theorem class_step_291 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 291 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 291 ≤ drawsBefore (291 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 291 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 291 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (291 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (291 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 291 (DefaultHeapClassStep.Effects spec mapping 291) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 291 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_291 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 291 pins table catalogue static 0x228 0xba07018c
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 291 pins table catalogue static 0x228 0xba07018c
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_291 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 291 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_291

#check "CURRENT_DECL heap class_step_292"
theorem class_step_292 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 292 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 292 ≤ drawsBefore (292 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 292 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 292 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (292 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (292 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 292 (DefaultHeapClassStep.Effects spec mapping 292) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 292 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_292 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_4
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 292 pins table catalogue static 0x22c 0x9bc47c87
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 292 pins table catalogue static 0x22c 0x9bc47c87
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_292 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 292 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_292

#check "CURRENT_DECL heap class_step_293"
theorem class_step_293 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 293 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 293 ≤ drawsBefore (293 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 293 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 293 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (293 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (293 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 293 (DefaultHeapClassStep.Effects spec mapping 293) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 293 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_293 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 293 pins table catalogue static 0x230 0xba0701ad
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 293 pins table catalogue static 0x230 0xba0701ad
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_293 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 293 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_293

#check "CURRENT_DECL heap class_step_294"
theorem class_step_294 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 294 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 294 ≤ drawsBefore (294 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 294 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 294 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (294 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (294 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 294 (DefaultHeapClassStep.Effects spec mapping 294) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 294 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_294 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 294 pins table catalogue static 0x234 0x9b057ca7
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 294 pins table catalogue static 0x234 0x9b057ca7
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_294 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 294 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_294

#check "CURRENT_DECL heap class_step_295"
theorem class_step_295 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 295 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 295 ≤ drawsBefore (295 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 295 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 295 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (295 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (295 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 295 (DefaultHeapClassStep.Effects spec mapping 295) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 295 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_295 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_12
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 295 pins table catalogue static 0x238 0xba0701ce
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 295 pins table catalogue static 0x238 0xba0701ce
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_295 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 295 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_295

end ReleaseProfile.DefaultHeapBranchRows
