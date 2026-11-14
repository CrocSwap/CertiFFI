-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapBranchStep
import DefaultBcondEventTail
import DefaultHeapCbzTail
import DefaultRetEventTail
import DefaultHeapCode
import HeapV2StepCerts.Residue.Step5Call
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable

#check "CURRENT_DECL heap step_15"
theorem step_15 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 15 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + HeapV2Compose.offsetOf (15 + 1)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 15 ≤ drawsBefore (15 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 15 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 15 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (15 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (15 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 15 (fun x fin => DefaultHeapBranchStep.LinkEffects spec mapping 15 x fin ∧ x.regs._PC = base + HeapV2Compose.offsetOf 15) []
    (fun x inv => by
      have target : NativeEntryCallerParts.blTarget 59#26 x = base + HeapV2Compose.offsetOf (15 + 1) := by
        rw [NativeEntryCallerRegisters.bl_target, inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      obtain ⟨fin, run, next, effect⟩ := DefaultHeapBranchStep.bl real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 15 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        59#26 (by decide) (by decide) x inv.body (by rw [target]; exact low) (controls inv) target nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 15 pins table catalogue static 60 2483028027
          (by decide) (by decide) _ (by decide) x inv.body.core)
      exact ⟨fin, run, next, effect, inv.body.core.v1.pc⟩)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_15 np rb vb r.1.holds r.1.value)
    (fun _ _ r field => RtSaved2.carry_bl (by decide) r.1.mem r.1.link r.2 field)
    (fun _ _ r => r.1.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 15 (by decide)) r.1.holds r.1.mem res.1, RtSaved3.carry_bl (by decide) r.1.mem r.1.link r.2 res.2⟩)
    (fun _ _ r => r.1.z) (fun _ _ r => r.1.events)

#print axioms step_15

#check "CURRENT_DECL heap step_150"
theorem step_150 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 150 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + HeapV2Compose.offsetOf (150 + 1)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 150 ≤ drawsBefore (150 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 150 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 150 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (150 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (150 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 150 (fun x fin => DefaultHeapBranchStep.LinkEffects spec mapping 150 x fin ∧ x.regs._PC = base + HeapV2Compose.offsetOf 150) []
    (fun x inv => by
      have target : NativeEntryCallerParts.blTarget 75#26 x = base + HeapV2Compose.offsetOf (150 + 1) := by
        rw [NativeEntryCallerRegisters.bl_target, inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      obtain ⟨fin, run, next, effect⟩ := DefaultHeapBranchStep.bl real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 150 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        75#26 (by decide) (by decide) x inv.body (by rw [target]; exact low) (controls inv) target nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 150 pins table catalogue static 76 2483028043
          (by decide) (by decide) _ (by decide) x inv.body.core)
      exact ⟨fin, run, next, effect, inv.body.core.v1.pc⟩)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_150 np rb vb r.1.holds r.1.value)
    (fun _ _ r field => RtSaved2.carry_bl (by decide) r.1.mem r.1.link r.2 field)
    (fun _ _ r => r.1.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 150 (by decide)) r.1.holds r.1.mem res.1, RtSaved3.carry_bl (by decide) r.1.mem r.1.link r.2 res.2⟩)
    (fun _ _ r => r.1.z) (fun _ _ r => r.1.events)

#print axioms step_150

#check "CURRENT_DECL heap step_252"
theorem step_252 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 252 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + HeapV2Compose.offsetOf (252 + 1)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 252 ≤ drawsBefore (252 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 252 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 252 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (252 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (252 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 252 (fun x fin => DefaultHeapBranchStep.LinkEffects spec mapping 252 x fin ∧ x.regs._PC = base + HeapV2Compose.offsetOf 252) []
    (fun x inv => by
      have target : NativeEntryCallerParts.blTarget 78#26 x = base + HeapV2Compose.offsetOf (252 + 1) := by
        rw [NativeEntryCallerRegisters.bl_target, inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      obtain ⟨fin, run, next, effect⟩ := DefaultHeapBranchStep.bl real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 252 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        78#26 (by decide) (by decide) x inv.body (by rw [target]; exact low) (controls inv) target nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 252 pins table catalogue static 88 2483028046
          (by decide) (by decide) _ (by decide) x inv.body.core)
      exact ⟨fin, run, next, effect, inv.body.core.v1.pc⟩)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_252 np rb vb r.1.holds r.1.value)
    (fun _ _ r field => RtSaved2.carry_bl (by decide) r.1.mem r.1.link r.2 field)
    (fun _ _ r => r.1.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 252 (by decide)) r.1.holds r.1.mem res.1, RtSaved3.carry_bl (by decide) r.1.mem r.1.link r.2 res.2⟩)
    (fun _ _ r => r.1.z) (fun _ _ r => r.1.events)

#print axioms step_252

#check "CURRENT_DECL heap step_146"
theorem step_146 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 146 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + HeapV2Compose.offsetOf (146 + 1)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 146 ≤ drawsBefore (146 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 146 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 146 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (146 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (146 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 146 (DefaultHeapBranchStep.BranchEffects spec mapping 146) []
    (fun x inv => by
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 146 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (EntryBodyRet.W 30#5) 94 (by decide) (by decide) x inv.body (DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) (by rw [RtSaved2.link_target (by decide) inv.lr]; exact low) _ (RtSaved2.link_target (by decide) inv.lr)) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 146 pins table catalogue static 0x140 0xd65f03c0
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_146 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 146 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_146

#check "CURRENT_DECL heap step_249"
theorem step_249 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 249 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + HeapV2Compose.offsetOf (249 + 1)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 249 ≤ drawsBefore (249 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 249 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 249 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (249 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (249 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 249 (DefaultHeapBranchStep.BranchEffects spec mapping 249) []
    (fun x inv => by
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 249 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (EntryBodyRet.W 30#5) 94 (by decide) (by decide) x inv.body (DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) (by rw [RtSaved2.link_target (by decide) inv.lr]; exact low) _ (RtSaved2.link_target (by decide) inv.lr)) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 249 pins table catalogue static 0x18c 0xd65f03c0
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_249 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 249 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_249

#check "CURRENT_DECL heap step_331"
theorem step_331 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 331 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + HeapV2Compose.offsetOf (331 + 1)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 331 ≤ drawsBefore (331 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 331 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 331 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (331 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (331 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 331 (DefaultHeapBranchStep.BranchEffects spec mapping 331) []
    (fun x inv => by
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 331 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (EntryBodyRet.W 30#5) 94 (by decide) (by decide) x inv.body (DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) (by rw [RtSaved2.link_target (by decide) inv.lr]; exact low) _ (RtSaved2.link_target (by decide) inv.lr)) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 331 pins table catalogue static 0x2c8 0xd65f03c0
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_331 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 331 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_331

end ReleaseProfile.DefaultHeapBranchRows
