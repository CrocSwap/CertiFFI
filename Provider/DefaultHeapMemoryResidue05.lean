-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapMemRows05
import HeapV2StepCerts.Residue.Step5Mem_05
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap mem_step_330"
theorem mem_step_330 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 330 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 330 + 2 ≤ capacity)
    (drawBound : drawsBefore 330 + 2 ≤ drawsBefore (330 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (330, 1, 16, 16, true)) true 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 330 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 330 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (330 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (330 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 330 (MemNextE.MemRE spec mapping 330 (RtSaved.accPA pins mapping (330, 1, 16, 16, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (330, 1, 16, 16, true)) true 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (330, 1, 16, 16, true)) true 16)
    (fun x inv => DefaultHeapMemRows.step_330 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_330 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 330 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_330).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_330

#check "CURRENT_DECL heap mem_step_351"
theorem mem_step_351 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 351 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 351 + 1 ≤ capacity)
    (drawBound : drawsBefore 351 + 1 ≤ drawsBefore (351 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (351, 0, (-64), 16, true)) true 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 351 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 351 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (351 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (351 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 351 (MemNextE.MemRE spec mapping 351 (RtSaved.accPA pins mapping (351, 0, (-64), 16, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (351, 0, (-64), 16, true)) true 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (351, 0, (-64), 16, true)) true 16)
    (fun x inv => DefaultHeapMemRows.step_351 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_351 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 351 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_351).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_351

#check "CURRENT_DECL heap mem_step_352"
theorem mem_step_352 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 352 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 352 + 1 ≤ capacity)
    (drawBound : drawsBefore 352 + 1 ≤ drawsBefore (352 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (352, 0, (-48), 16, true)) true 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 352 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 352 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (352 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (352 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 352 (MemNextE.MemRE spec mapping 352 (RtSaved.accPA pins mapping (352, 0, (-48), 16, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (352, 0, (-48), 16, true)) true 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (352, 0, (-48), 16, true)) true 16)
    (fun x inv => DefaultHeapMemRows.step_352 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_352 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 352 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_352).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_352

#check "CURRENT_DECL heap mem_step_353"
theorem mem_step_353 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 353 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 353 + 1 ≤ capacity)
    (drawBound : drawsBefore 353 + 1 ≤ drawsBefore (353 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (353, 0, (-32), 16, true)) true 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 353 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 353 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (353 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (353 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 353 (MemNextE.MemRE spec mapping 353 (RtSaved.accPA pins mapping (353, 0, (-32), 16, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (353, 0, (-32), 16, true)) true 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (353, 0, (-32), 16, true)) true 16)
    (fun x inv => DefaultHeapMemRows.step_353 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_353 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 353 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_353).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_353

#check "CURRENT_DECL heap mem_step_354"
theorem mem_step_354 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 354 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 354 + 1 ≤ capacity)
    (drawBound : drawsBefore 354 + 1 ≤ drawsBefore (354 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (354, 0, (-16), 16, false)) false 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 354 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 354 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (354 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (354 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 354 (MemNextE.MemRE spec mapping 354 (fun _ => False) (RtSaved3.MemFacts2.LdpPay2 pins mapping (354, 0, (-16), 16, false) (19#5) (30#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (354, 0, (-16), 16, false)) false 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (354, 0, (-16), 16, false)) false 16)
    (fun x inv => DefaultHeapMemRows.step_354 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_354 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => RtSaved2.field_ldp354 mapped (RtSaved3.MemFacts2.LdpPay2.toPay (MemNextE.MemRE.toR r).2.2.2.1) field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 354 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, RtSaved3.field_ldp354 mapped (MemNextE.MemRE.toR r).2.2.2.1 res.2⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_354

#check "CURRENT_DECL heap mem_step_355"
theorem mem_step_355 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 355 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 355 + 1 ≤ capacity)
    (drawBound : drawsBefore 355 + 1 ≤ drawsBefore (355 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (355, 0, (-16), 16, true)) true 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 355 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 355 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (355 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (355 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 355 (MemNextE.MemRE spec mapping 355 (RtSaved.accPA pins mapping (355, 0, (-16), 16, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (355, 0, (-16), 16, true)) true 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (355, 0, (-16), 16, true)) true 16)
    (fun x inv => DefaultHeapMemRows.step_355 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_355 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun lo hi => absurd (And.intro lo hi) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 355 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_355).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun lo hi => absurd (And.intro lo hi) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_355

end ReleaseProfile.DefaultHeapBranchRows
