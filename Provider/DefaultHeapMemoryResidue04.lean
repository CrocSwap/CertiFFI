-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapMemRows04
import HeapV2StepCerts.Residue.Step5Mem_04
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap mem_step_198"
theorem mem_step_198 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 198 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 198 + 1 ≤ capacity)
    (drawBound : drawsBefore 198 + 1 ≤ drawsBefore (198 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (198, 1, 15, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 198 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 198 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (198 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (198 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 198 (MemNextE.MemRE spec mapping 198 (RtSaved.accPA pins mapping (198, 1, 15, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (198, 1, 15, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (198, 1, 15, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_198 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_198 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 198 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_198).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_198

#check "CURRENT_DECL heap mem_step_201"
theorem mem_step_201 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 201 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 201 + 1 ≤ capacity)
    (drawBound : drawsBefore 201 + 1 ≤ drawsBefore (201 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (201, 1, 16, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 201 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 201 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (201 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (201 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 201 (MemNextE.MemRE spec mapping 201 (RtSaved.accPA pins mapping (201, 1, 16, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (201, 1, 16, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (201, 1, 16, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_201 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_201 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 201 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_201).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_201

#check "CURRENT_DECL heap mem_step_204"
theorem mem_step_204 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 204 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 204 + 1 ≤ capacity)
    (drawBound : drawsBefore 204 + 1 ≤ drawsBefore (204 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (204, 1, 17, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 204 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 204 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (204 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (204 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 204 (MemNextE.MemRE spec mapping 204 (RtSaved.accPA pins mapping (204, 1, 17, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (204, 1, 17, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (204, 1, 17, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_204 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_204 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 204 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_204).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_204

#check "CURRENT_DECL heap mem_step_207"
theorem mem_step_207 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 207 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 207 + 1 ≤ capacity)
    (drawBound : drawsBefore 207 + 1 ≤ drawsBefore (207 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (207, 1, 18, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 207 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 207 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (207 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (207 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 207 (MemNextE.MemRE spec mapping 207 (RtSaved.accPA pins mapping (207, 1, 18, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (207, 1, 18, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (207, 1, 18, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_207 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_207 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 207 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_207).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_207

#check "CURRENT_DECL heap mem_step_210"
theorem mem_step_210 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 210 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 210 + 1 ≤ capacity)
    (drawBound : drawsBefore 210 + 1 ≤ drawsBefore (210 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (210, 1, 19, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 210 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 210 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (210 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (210 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 210 (MemNextE.MemRE spec mapping 210 (RtSaved.accPA pins mapping (210, 1, 19, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (210, 1, 19, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (210, 1, 19, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_210 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_210 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 210 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_210).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_210

#check "CURRENT_DECL heap mem_step_213"
theorem mem_step_213 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 213 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 213 + 1 ≤ capacity)
    (drawBound : drawsBefore 213 + 1 ≤ drawsBefore (213 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (213, 1, 20, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 213 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 213 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (213 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (213 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 213 (MemNextE.MemRE spec mapping 213 (RtSaved.accPA pins mapping (213, 1, 20, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (213, 1, 20, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (213, 1, 20, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_213 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_213 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 213 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_213).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_213

#check "CURRENT_DECL heap mem_step_216"
theorem mem_step_216 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 216 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 216 + 1 ≤ capacity)
    (drawBound : drawsBefore 216 + 1 ≤ drawsBefore (216 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (216, 1, 21, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 216 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 216 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (216 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (216 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 216 (MemNextE.MemRE spec mapping 216 (RtSaved.accPA pins mapping (216, 1, 21, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (216, 1, 21, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (216, 1, 21, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_216 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_216 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 216 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_216).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_216

#check "CURRENT_DECL heap mem_step_219"
theorem mem_step_219 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 219 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 219 + 1 ≤ capacity)
    (drawBound : drawsBefore 219 + 1 ≤ drawsBefore (219 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (219, 1, 22, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 219 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 219 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (219 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (219 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 219 (MemNextE.MemRE spec mapping 219 (RtSaved.accPA pins mapping (219, 1, 22, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (219, 1, 22, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (219, 1, 22, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_219 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_219 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 219 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_219).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_219

#check "CURRENT_DECL heap mem_step_222"
theorem mem_step_222 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 222 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 222 + 1 ≤ capacity)
    (drawBound : drawsBefore 222 + 1 ≤ drawsBefore (222 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (222, 1, 23, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 222 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 222 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (222 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (222 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 222 (MemNextE.MemRE spec mapping 222 (RtSaved.accPA pins mapping (222, 1, 23, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (222, 1, 23, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (222, 1, 23, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_222 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_222 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 222 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_222).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_222

#check "CURRENT_DECL heap mem_step_225"
theorem mem_step_225 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 225 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 225 + 1 ≤ capacity)
    (drawBound : drawsBefore 225 + 1 ≤ drawsBefore (225 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (225, 1, 24, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 225 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 225 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (225 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (225 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 225 (MemNextE.MemRE spec mapping 225 (RtSaved.accPA pins mapping (225, 1, 24, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (225, 1, 24, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (225, 1, 24, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_225 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_225 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 225 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_225).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_225

#check "CURRENT_DECL heap mem_step_228"
theorem mem_step_228 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 228 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 228 + 1 ≤ capacity)
    (drawBound : drawsBefore 228 + 1 ≤ drawsBefore (228 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (228, 1, 25, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 228 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 228 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (228 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (228 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 228 (MemNextE.MemRE spec mapping 228 (RtSaved.accPA pins mapping (228, 1, 25, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (228, 1, 25, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (228, 1, 25, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_228 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_228 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 228 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_228).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_228

#check "CURRENT_DECL heap mem_step_231"
theorem mem_step_231 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 231 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 231 + 1 ≤ capacity)
    (drawBound : drawsBefore 231 + 1 ≤ drawsBefore (231 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (231, 1, 26, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 231 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 231 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (231 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (231 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 231 (MemNextE.MemRE spec mapping 231 (RtSaved.accPA pins mapping (231, 1, 26, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (231, 1, 26, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (231, 1, 26, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_231 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_231 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 231 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_231).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_231

#check "CURRENT_DECL heap mem_step_234"
theorem mem_step_234 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 234 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 234 + 1 ≤ capacity)
    (drawBound : drawsBefore 234 + 1 ≤ drawsBefore (234 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (234, 1, 27, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 234 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 234 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (234 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (234 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 234 (MemNextE.MemRE spec mapping 234 (RtSaved.accPA pins mapping (234, 1, 27, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (234, 1, 27, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (234, 1, 27, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_234 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_234 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 234 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_234).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_234

#check "CURRENT_DECL heap mem_step_237"
theorem mem_step_237 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 237 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 237 + 1 ≤ capacity)
    (drawBound : drawsBefore 237 + 1 ≤ drawsBefore (237 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (237, 1, 28, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 237 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 237 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (237 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (237 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 237 (MemNextE.MemRE spec mapping 237 (RtSaved.accPA pins mapping (237, 1, 28, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (237, 1, 28, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (237, 1, 28, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_237 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_237 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 237 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_237).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_237

#check "CURRENT_DECL heap mem_step_240"
theorem mem_step_240 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 240 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 240 + 1 ≤ capacity)
    (drawBound : drawsBefore 240 + 1 ≤ drawsBefore (240 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (240, 1, 29, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 240 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 240 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (240 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (240 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 240 (MemNextE.MemRE spec mapping 240 (RtSaved.accPA pins mapping (240, 1, 29, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (240, 1, 29, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (240, 1, 29, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_240 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_240 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 240 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_240).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_240

#check "CURRENT_DECL heap mem_step_243"
theorem mem_step_243 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 243 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 243 + 1 ≤ capacity)
    (drawBound : drawsBefore 243 + 1 ≤ drawsBefore (243 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (243, 1, 30, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 243 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 243 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (243 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (243 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 243 (MemNextE.MemRE spec mapping 243 (RtSaved.accPA pins mapping (243, 1, 30, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (243, 1, 30, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (243, 1, 30, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_243 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_243 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 243 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_243).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_243

#check "CURRENT_DECL heap mem_step_246"
theorem mem_step_246 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 246 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 246 + 1 ≤ capacity)
    (drawBound : drawsBefore 246 + 1 ≤ drawsBefore (246 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (246, 1, 31, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 246 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 246 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (246 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (246 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 246 (MemNextE.MemRE spec mapping 246 (RtSaved.accPA pins mapping (246, 1, 31, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (246, 1, 31, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (246, 1, 31, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_246 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_246 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 246 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_246).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_246

#check "CURRENT_DECL heap mem_step_253"
theorem mem_step_253 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 253 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 253 + 2 ≤ capacity)
    (drawBound : drawsBefore 253 + 2 ≤ drawsBefore (253 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (253, 0, (-64), 16, false)) false 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 253 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 253 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (253 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (253 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 253 (MemNextE.MemRE spec mapping 253 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (253, 0, (-64), 16, false)) false 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (253, 0, (-64), 16, false)) false 16)
    (fun x inv => DefaultHeapMemRows.step_253 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_253 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 253 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_253

#check "CURRENT_DECL heap mem_step_256"
theorem mem_step_256 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 256 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 256 + 2 ≤ capacity)
    (drawBound : drawsBefore 256 + 2 ≤ drawsBefore (256 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (256, 0, (-48), 16, false)) false 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 256 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 256 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (256 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (256 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 256 (MemNextE.MemRE spec mapping 256 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (256, 0, (-48), 16, false)) false 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (256, 0, (-48), 16, false)) false 16)
    (fun x inv => DefaultHeapMemRows.step_256 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_256 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 256 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_256

#check "CURRENT_DECL heap mem_step_329"
theorem mem_step_329 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 329 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 329 + 2 ≤ capacity)
    (drawBound : drawsBefore 329 + 2 ≤ drawsBefore (329 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (329, 1, 0, 16, true)) true 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 329 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 329 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (329 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (329 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 329 (MemNextE.MemRE spec mapping 329 (RtSaved.accPA pins mapping (329, 1, 0, 16, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (329, 1, 0, 16, true)) true 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (329, 1, 0, 16, true)) true 16)
    (fun x inv => DefaultHeapMemRows.step_329 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_329 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 329 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_329).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_329

end ReleaseProfile.DefaultHeapBranchRows
