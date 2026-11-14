-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapMemRows02
import HeapV2StepCerts.Residue.Step5Mem_02
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap mem_step_95"
theorem mem_step_95 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 95 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 95 + 1 ≤ capacity)
    (drawBound : drawsBefore 95 + 1 ≤ drawsBefore (95 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (95, 0, (-45), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 95 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 95 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (95 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (95 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 95 (MemNextE.MemRE spec mapping 95 (RtSaved.accPA pins mapping (95, 0, (-45), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (95, 0, (-45), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (95, 0, (-45), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_95 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_95 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 95 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_95).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_95

#check "CURRENT_DECL heap mem_step_98"
theorem mem_step_98 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 98 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 98 + 1 ≤ capacity)
    (drawBound : drawsBefore 98 + 1 ≤ drawsBefore (98 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (98, 2, 20, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 98 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 98 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (98 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (98 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 98 (MemNextE.MemRE spec mapping 98 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (98, 2, 20, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (98, 2, 20, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_98 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_98 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 98 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_98

#check "CURRENT_DECL heap mem_step_99"
theorem mem_step_99 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 99 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 99 + 1 ≤ capacity)
    (drawBound : drawsBefore 99 + 1 ≤ drawsBefore (99 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (99, 0, (-44), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 99 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 99 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (99 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (99 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 99 (MemNextE.MemRE spec mapping 99 (RtSaved.accPA pins mapping (99, 0, (-44), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (99, 0, (-44), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (99, 0, (-44), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_99 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_99 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 99 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_99).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_99

#check "CURRENT_DECL heap mem_step_102"
theorem mem_step_102 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 102 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 102 + 1 ≤ capacity)
    (drawBound : drawsBefore 102 + 1 ≤ drawsBefore (102 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (102, 2, 21, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 102 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 102 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (102 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (102 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 102 (MemNextE.MemRE spec mapping 102 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (102, 2, 21, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (102, 2, 21, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_102 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_102 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 102 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_102

#check "CURRENT_DECL heap mem_step_103"
theorem mem_step_103 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 103 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 103 + 1 ≤ capacity)
    (drawBound : drawsBefore 103 + 1 ≤ drawsBefore (103 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (103, 0, (-43), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 103 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 103 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (103 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (103 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 103 (MemNextE.MemRE spec mapping 103 (RtSaved.accPA pins mapping (103, 0, (-43), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (103, 0, (-43), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (103, 0, (-43), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_103 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_103 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 103 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_103).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_103

#check "CURRENT_DECL heap mem_step_106"
theorem mem_step_106 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 106 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 106 + 1 ≤ capacity)
    (drawBound : drawsBefore 106 + 1 ≤ drawsBefore (106 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (106, 2, 22, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 106 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 106 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (106 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (106 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 106 (MemNextE.MemRE spec mapping 106 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (106, 2, 22, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (106, 2, 22, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_106 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_106 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 106 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_106

#check "CURRENT_DECL heap mem_step_107"
theorem mem_step_107 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 107 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 107 + 1 ≤ capacity)
    (drawBound : drawsBefore 107 + 1 ≤ drawsBefore (107 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (107, 0, (-42), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 107 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 107 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (107 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (107 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 107 (MemNextE.MemRE spec mapping 107 (RtSaved.accPA pins mapping (107, 0, (-42), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (107, 0, (-42), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (107, 0, (-42), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_107 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_107 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 107 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_107).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_107

#check "CURRENT_DECL heap mem_step_110"
theorem mem_step_110 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 110 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 110 + 1 ≤ capacity)
    (drawBound : drawsBefore 110 + 1 ≤ drawsBefore (110 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (110, 2, 23, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 110 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 110 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (110 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (110 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 110 (MemNextE.MemRE spec mapping 110 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (110, 2, 23, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (110, 2, 23, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_110 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_110 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 110 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_110

#check "CURRENT_DECL heap mem_step_111"
theorem mem_step_111 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 111 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 111 + 1 ≤ capacity)
    (drawBound : drawsBefore 111 + 1 ≤ drawsBefore (111 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (111, 0, (-41), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 111 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 111 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (111 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (111 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 111 (MemNextE.MemRE spec mapping 111 (RtSaved.accPA pins mapping (111, 0, (-41), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (111, 0, (-41), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (111, 0, (-41), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_111 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_111 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 111 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_111).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_111

#check "CURRENT_DECL heap mem_step_114"
theorem mem_step_114 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 114 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 114 + 1 ≤ capacity)
    (drawBound : drawsBefore 114 + 1 ≤ drawsBefore (114 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (114, 2, 24, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 114 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 114 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (114 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (114 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 114 (MemNextE.MemRE spec mapping 114 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (114, 2, 24, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (114, 2, 24, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_114 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_114 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 114 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_114

#check "CURRENT_DECL heap mem_step_115"
theorem mem_step_115 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 115 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 115 + 1 ≤ capacity)
    (drawBound : drawsBefore 115 + 1 ≤ drawsBefore (115 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (115, 0, (-40), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 115 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 115 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (115 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (115 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 115 (MemNextE.MemRE spec mapping 115 (RtSaved.accPA pins mapping (115, 0, (-40), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (115, 0, (-40), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (115, 0, (-40), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_115 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_115 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 115 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_115).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_115

#check "CURRENT_DECL heap mem_step_118"
theorem mem_step_118 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 118 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 118 + 1 ≤ capacity)
    (drawBound : drawsBefore 118 + 1 ≤ drawsBefore (118 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (118, 2, 25, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 118 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 118 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (118 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (118 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 118 (MemNextE.MemRE spec mapping 118 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (118, 2, 25, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (118, 2, 25, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_118 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_118 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 118 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_118

#check "CURRENT_DECL heap mem_step_119"
theorem mem_step_119 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 119 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 119 + 1 ≤ capacity)
    (drawBound : drawsBefore 119 + 1 ≤ drawsBefore (119 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (119, 0, (-39), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 119 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 119 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (119 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (119 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 119 (MemNextE.MemRE spec mapping 119 (RtSaved.accPA pins mapping (119, 0, (-39), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (119, 0, (-39), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (119, 0, (-39), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_119 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_119 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 119 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_119).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_119

#check "CURRENT_DECL heap mem_step_122"
theorem mem_step_122 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 122 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 122 + 1 ≤ capacity)
    (drawBound : drawsBefore 122 + 1 ≤ drawsBefore (122 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (122, 2, 26, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 122 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 122 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (122 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (122 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 122 (MemNextE.MemRE spec mapping 122 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (122, 2, 26, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (122, 2, 26, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_122 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_122 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 122 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_122

#check "CURRENT_DECL heap mem_step_123"
theorem mem_step_123 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 123 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 123 + 1 ≤ capacity)
    (drawBound : drawsBefore 123 + 1 ≤ drawsBefore (123 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (123, 0, (-38), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 123 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 123 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (123 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (123 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 123 (MemNextE.MemRE spec mapping 123 (RtSaved.accPA pins mapping (123, 0, (-38), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (123, 0, (-38), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (123, 0, (-38), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_123 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_123 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 123 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_123).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_123

#check "CURRENT_DECL heap mem_step_126"
theorem mem_step_126 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 126 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 126 + 1 ≤ capacity)
    (drawBound : drawsBefore 126 + 1 ≤ drawsBefore (126 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (126, 2, 27, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 126 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 126 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (126 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (126 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 126 (MemNextE.MemRE spec mapping 126 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (126, 2, 27, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (126, 2, 27, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_126 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_126 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 126 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_126

#check "CURRENT_DECL heap mem_step_127"
theorem mem_step_127 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 127 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 127 + 1 ≤ capacity)
    (drawBound : drawsBefore 127 + 1 ≤ drawsBefore (127 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (127, 0, (-37), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 127 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 127 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (127 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (127 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 127 (MemNextE.MemRE spec mapping 127 (RtSaved.accPA pins mapping (127, 0, (-37), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (127, 0, (-37), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (127, 0, (-37), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_127 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_127 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 127 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_127).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_127

#check "CURRENT_DECL heap mem_step_130"
theorem mem_step_130 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 130 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 130 + 1 ≤ capacity)
    (drawBound : drawsBefore 130 + 1 ≤ drawsBefore (130 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (130, 2, 28, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 130 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 130 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (130 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (130 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 130 (MemNextE.MemRE spec mapping 130 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (130, 2, 28, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (130, 2, 28, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_130 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_130 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 130 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_130

#check "CURRENT_DECL heap mem_step_131"
theorem mem_step_131 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 131 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 131 + 1 ≤ capacity)
    (drawBound : drawsBefore 131 + 1 ≤ drawsBefore (131 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (131, 0, (-36), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 131 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 131 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (131 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (131 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 131 (MemNextE.MemRE spec mapping 131 (RtSaved.accPA pins mapping (131, 0, (-36), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (131, 0, (-36), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (131, 0, (-36), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_131 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_131 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 131 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_131).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_131

#check "CURRENT_DECL heap mem_step_134"
theorem mem_step_134 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 134 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 134 + 1 ≤ capacity)
    (drawBound : drawsBefore 134 + 1 ≤ drawsBefore (134 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (134, 2, 29, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 134 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 134 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (134 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (134 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 134 (MemNextE.MemRE spec mapping 134 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (134, 2, 29, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (134, 2, 29, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_134 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_134 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 134 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_134

end ReleaseProfile.DefaultHeapBranchRows
