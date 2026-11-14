-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import HeapScalarTagCheck.Tails
import DefaultHeapClassStep
import DefaultHeapCode
import HeapV2StepCerts.Residue.ZSeg_06
import HeapV2StepCerts.Residue.ZSeg_07
import HeapV2StepCerts.Residue.ZSeg_08
import HeapV2StepCerts.Residue.Step5Class_03
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap class_step_199"
theorem class_step_199 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 199 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 199 ≤ drawsBefore (199 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 199 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 199 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (199 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (199 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 199 (DefaultHeapClassStep.Effects spec mapping 199) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 199 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_199 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 199 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 199 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_199 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 199 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_199

#check "CURRENT_DECL heap class_step_202"
theorem class_step_202 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 202 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 202 ≤ drawsBefore (202 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 202 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 202 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (202 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (202 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 202 (DefaultHeapClassStep.Effects spec mapping 202) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 202 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_202 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 202 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 202 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_202 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 202 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_202

#check "CURRENT_DECL heap class_step_205"
theorem class_step_205 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 205 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 205 ≤ drawsBefore (205 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 205 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 205 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (205 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (205 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 205 (DefaultHeapClassStep.Effects spec mapping 205) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 205 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_205 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 205 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 205 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_205 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 205 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_205

#check "CURRENT_DECL heap class_step_208"
theorem class_step_208 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 208 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 208 ≤ drawsBefore (208 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 208 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 208 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (208 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (208 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 208 (DefaultHeapClassStep.Effects spec mapping 208) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 208 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_208 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 208 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 208 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_208 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 208 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_208

#check "CURRENT_DECL heap class_step_211"
theorem class_step_211 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 211 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 211 ≤ drawsBefore (211 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 211 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 211 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (211 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (211 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 211 (DefaultHeapClassStep.Effects spec mapping 211) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 211 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_211 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 211 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 211 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_211 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 211 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_211

#check "CURRENT_DECL heap class_step_214"
theorem class_step_214 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 214 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 214 ≤ drawsBefore (214 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 214 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 214 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (214 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (214 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 214 (DefaultHeapClassStep.Effects spec mapping 214) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 214 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_214 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 214 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 214 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_214 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 214 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_214

#check "CURRENT_DECL heap class_step_217"
theorem class_step_217 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 217 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 217 ≤ drawsBefore (217 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 217 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 217 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (217 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (217 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 217 (DefaultHeapClassStep.Effects spec mapping 217) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 217 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_217 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 217 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 217 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_217 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 217 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_217

#check "CURRENT_DECL heap class_step_220"
theorem class_step_220 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 220 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 220 ≤ drawsBefore (220 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 220 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 220 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (220 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (220 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 220 (DefaultHeapClassStep.Effects spec mapping 220) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 220 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_220 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 220 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 220 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_220 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 220 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_220

#check "CURRENT_DECL heap class_step_223"
theorem class_step_223 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 223 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 223 ≤ drawsBefore (223 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 223 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 223 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (223 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (223 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 223 (DefaultHeapClassStep.Effects spec mapping 223) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 223 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_223 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 223 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 223 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_223 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 223 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_223

#check "CURRENT_DECL heap class_step_226"
theorem class_step_226 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 226 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 226 ≤ drawsBefore (226 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 226 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 226 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (226 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (226 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 226 (DefaultHeapClassStep.Effects spec mapping 226) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 226 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_226 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 226 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 226 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_226 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 226 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_226

#check "CURRENT_DECL heap class_step_229"
theorem class_step_229 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 229 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 229 ≤ drawsBefore (229 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 229 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 229 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (229 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (229 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 229 (DefaultHeapClassStep.Effects spec mapping 229) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 229 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_229 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 229 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 229 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_229 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 229 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_229

#check "CURRENT_DECL heap class_step_232"
theorem class_step_232 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 232 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 232 ≤ drawsBefore (232 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 232 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 232 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (232 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (232 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 232 (DefaultHeapClassStep.Effects spec mapping 232) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 232 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_232 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 232 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 232 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_232 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 232 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_232

#check "CURRENT_DECL heap class_step_235"
theorem class_step_235 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 235 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 235 ≤ drawsBefore (235 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 235 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 235 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (235 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (235 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 235 (DefaultHeapClassStep.Effects spec mapping 235) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 235 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_235 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 235 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 235 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_235 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 235 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_235

#check "CURRENT_DECL heap class_step_238"
theorem class_step_238 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 238 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 238 ≤ drawsBefore (238 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 238 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 238 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (238 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (238 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 238 (DefaultHeapClassStep.Effects spec mapping 238) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 238 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_238 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 238 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 238 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_238 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 238 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_238

#check "CURRENT_DECL heap class_step_241"
theorem class_step_241 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 241 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 241 ≤ drawsBefore (241 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 241 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 241 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (241 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (241 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 241 (DefaultHeapClassStep.Effects spec mapping 241) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 241 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_241 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 241 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 241 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_241 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 241 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_241

#check "CURRENT_DECL heap class_step_244"
theorem class_step_244 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 244 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 244 ≤ drawsBefore (244 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 244 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 244 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (244 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (244 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 244 (DefaultHeapClassStep.Effects spec mapping 244) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 244 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_244 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 244 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 244 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_244 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 244 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_244

#check "CURRENT_DECL heap class_step_247"
theorem class_step_247 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 247 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 247 ≤ drawsBefore (247 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 247 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 247 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (247 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (247 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 247 (DefaultHeapClassStep.Effects spec mapping 247) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 247 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.tailW_247 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_19
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 247 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 247 pins table catalogue static 0x184 0xf1000442
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_247 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 247 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_247

#check "CURRENT_DECL heap class_step_250"
theorem class_step_250 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 250 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 250 ≤ drawsBefore (250 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 250 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 250 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (250 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (250 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 250 (DefaultHeapClassStep.Effects spec mapping 250) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 250 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_250 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_9
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 250 pins table catalogue static 0x50 0xaa1303e0
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 250 pins table catalogue static 0x50 0xaa1303e0
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_250 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 250 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_250

#check "CURRENT_DECL heap class_step_251"
theorem class_step_251 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 251 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 251 ≤ drawsBefore (251 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 251 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 251 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (251 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (251 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 251 (DefaultHeapClassStep.Effects spec mapping 251) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 251 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_251 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_10
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 251 pins table catalogue static 0x54 0x910003e1
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 251 pins table catalogue static 0x54 0x910003e1
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_251 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 251 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_251

#check "CURRENT_DECL heap class_step_254"
theorem class_step_254 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 254 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 254 ≤ drawsBefore (254 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 254 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 254 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (254 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (254 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 254 (DefaultHeapClassStep.Effects spec mapping 254) []
    (fun x inv => DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 254 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
      _ _ _ x inv.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_254 real x))
      (by
        apply HeapScalarTagCheck.Tails.tail_3
        all_goals first | decide | constructor)
      (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 254 pins table catalogue static 0x194 0x9b037c49
        (by decide) (by decide) (by decide) x inv.body.core) nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 254 pins table catalogue static 0x194 0x9b037c49
        (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_254 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 254 (by decide)) r.holds r.mem res.1, RtSaved3.carry_class (by decide) (by decide) (by decide) (by decide) r.mem r.holds res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms class_step_254

end ReleaseProfile.DefaultHeapBranchRows
