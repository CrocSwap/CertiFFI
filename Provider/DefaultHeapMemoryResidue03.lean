-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapMemRows03
import HeapV2StepCerts.Residue.Step5Mem_03
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap mem_step_135"
theorem mem_step_135 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 135 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 135 + 1 ≤ capacity)
    (drawBound : drawsBefore 135 + 1 ≤ drawsBefore (135 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (135, 0, (-35), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 135 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 135 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (135 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (135 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 135 (MemNextE.MemRE spec mapping 135 (RtSaved.accPA pins mapping (135, 0, (-35), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (135, 0, (-35), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (135, 0, (-35), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_135 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_135 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 135 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_135).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_135

#check "CURRENT_DECL heap mem_step_138"
theorem mem_step_138 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 138 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 138 + 1 ≤ capacity)
    (drawBound : drawsBefore 138 + 1 ≤ drawsBefore (138 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (138, 2, 30, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 138 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 138 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (138 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (138 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 138 (MemNextE.MemRE spec mapping 138 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (138, 2, 30, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (138, 2, 30, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_138 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_138 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 138 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_138

#check "CURRENT_DECL heap mem_step_139"
theorem mem_step_139 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 139 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 139 + 1 ≤ capacity)
    (drawBound : drawsBefore 139 + 1 ≤ drawsBefore (139 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (139, 0, (-34), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 139 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 139 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (139 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (139 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 139 (MemNextE.MemRE spec mapping 139 (RtSaved.accPA pins mapping (139, 0, (-34), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (139, 0, (-34), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (139, 0, (-34), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_139 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_139 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 139 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_139).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_139

#check "CURRENT_DECL heap mem_step_142"
theorem mem_step_142 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 142 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 142 + 1 ≤ capacity)
    (drawBound : drawsBefore 142 + 1 ≤ drawsBefore (142 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (142, 2, 31, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 142 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 142 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (142 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (142 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 142 (MemNextE.MemRE spec mapping 142 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (142, 2, 31, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (142, 2, 31, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_142 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_142 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 142 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_142

#check "CURRENT_DECL heap mem_step_143"
theorem mem_step_143 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 143 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 143 + 1 ≤ capacity)
    (drawBound : drawsBefore 143 + 1 ≤ drawsBefore (143 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (143, 0, (-33), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 143 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 143 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (143 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (143 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 143 (MemNextE.MemRE spec mapping 143 (RtSaved.accPA pins mapping (143, 0, (-33), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (143, 0, (-33), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (143, 0, (-33), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_143 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_143 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 143 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_143).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_143

#check "CURRENT_DECL heap mem_step_153"
theorem mem_step_153 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 153 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 153 + 1 ≤ capacity)
    (drawBound : drawsBefore 153 + 1 ≤ drawsBefore (153 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (153, 1, 0, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 153 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 153 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (153 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (153 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 153 (MemNextE.MemRE spec mapping 153 (RtSaved.accPA pins mapping (153, 1, 0, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (153, 1, 0, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (153, 1, 0, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_153 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_153 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 153 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_153).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_153

#check "CURRENT_DECL heap mem_step_156"
theorem mem_step_156 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 156 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 156 + 1 ≤ capacity)
    (drawBound : drawsBefore 156 + 1 ≤ drawsBefore (156 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (156, 1, 1, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 156 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 156 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (156 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (156 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 156 (MemNextE.MemRE spec mapping 156 (RtSaved.accPA pins mapping (156, 1, 1, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (156, 1, 1, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (156, 1, 1, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_156 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_156 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 156 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_156).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_156

#check "CURRENT_DECL heap mem_step_159"
theorem mem_step_159 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 159 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 159 + 1 ≤ capacity)
    (drawBound : drawsBefore 159 + 1 ≤ drawsBefore (159 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (159, 1, 2, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 159 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 159 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (159 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (159 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 159 (MemNextE.MemRE spec mapping 159 (RtSaved.accPA pins mapping (159, 1, 2, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (159, 1, 2, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (159, 1, 2, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_159 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_159 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 159 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_159).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_159

#check "CURRENT_DECL heap mem_step_162"
theorem mem_step_162 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 162 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 162 + 1 ≤ capacity)
    (drawBound : drawsBefore 162 + 1 ≤ drawsBefore (162 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (162, 1, 3, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 162 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 162 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (162 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (162 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 162 (MemNextE.MemRE spec mapping 162 (RtSaved.accPA pins mapping (162, 1, 3, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (162, 1, 3, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (162, 1, 3, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_162 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_162 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 162 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_162).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_162

#check "CURRENT_DECL heap mem_step_165"
theorem mem_step_165 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 165 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 165 + 1 ≤ capacity)
    (drawBound : drawsBefore 165 + 1 ≤ drawsBefore (165 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (165, 1, 4, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 165 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 165 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (165 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (165 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 165 (MemNextE.MemRE spec mapping 165 (RtSaved.accPA pins mapping (165, 1, 4, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (165, 1, 4, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (165, 1, 4, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_165 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_165 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 165 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_165).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_165

#check "CURRENT_DECL heap mem_step_168"
theorem mem_step_168 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 168 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 168 + 1 ≤ capacity)
    (drawBound : drawsBefore 168 + 1 ≤ drawsBefore (168 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (168, 1, 5, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 168 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 168 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (168 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (168 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 168 (MemNextE.MemRE spec mapping 168 (RtSaved.accPA pins mapping (168, 1, 5, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (168, 1, 5, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (168, 1, 5, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_168 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_168 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 168 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_168).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_168

#check "CURRENT_DECL heap mem_step_171"
theorem mem_step_171 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 171 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 171 + 1 ≤ capacity)
    (drawBound : drawsBefore 171 + 1 ≤ drawsBefore (171 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (171, 1, 6, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 171 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 171 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (171 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (171 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 171 (MemNextE.MemRE spec mapping 171 (RtSaved.accPA pins mapping (171, 1, 6, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (171, 1, 6, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (171, 1, 6, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_171 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_171 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 171 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_171).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_171

#check "CURRENT_DECL heap mem_step_174"
theorem mem_step_174 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 174 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 174 + 1 ≤ capacity)
    (drawBound : drawsBefore 174 + 1 ≤ drawsBefore (174 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (174, 1, 7, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 174 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 174 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (174 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (174 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 174 (MemNextE.MemRE spec mapping 174 (RtSaved.accPA pins mapping (174, 1, 7, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (174, 1, 7, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (174, 1, 7, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_174 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_174 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 174 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_174).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_174

#check "CURRENT_DECL heap mem_step_177"
theorem mem_step_177 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 177 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 177 + 1 ≤ capacity)
    (drawBound : drawsBefore 177 + 1 ≤ drawsBefore (177 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (177, 1, 8, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 177 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 177 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (177 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (177 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 177 (MemNextE.MemRE spec mapping 177 (RtSaved.accPA pins mapping (177, 1, 8, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (177, 1, 8, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (177, 1, 8, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_177 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_177 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 177 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_177).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_177

#check "CURRENT_DECL heap mem_step_180"
theorem mem_step_180 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 180 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 180 + 1 ≤ capacity)
    (drawBound : drawsBefore 180 + 1 ≤ drawsBefore (180 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (180, 1, 9, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 180 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 180 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (180 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (180 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 180 (MemNextE.MemRE spec mapping 180 (RtSaved.accPA pins mapping (180, 1, 9, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (180, 1, 9, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (180, 1, 9, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_180 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_180 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 180 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_180).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_180

#check "CURRENT_DECL heap mem_step_183"
theorem mem_step_183 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 183 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 183 + 1 ≤ capacity)
    (drawBound : drawsBefore 183 + 1 ≤ drawsBefore (183 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (183, 1, 10, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 183 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 183 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (183 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (183 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 183 (MemNextE.MemRE spec mapping 183 (RtSaved.accPA pins mapping (183, 1, 10, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (183, 1, 10, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (183, 1, 10, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_183 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_183 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 183 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_183).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_183

#check "CURRENT_DECL heap mem_step_186"
theorem mem_step_186 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 186 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 186 + 1 ≤ capacity)
    (drawBound : drawsBefore 186 + 1 ≤ drawsBefore (186 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (186, 1, 11, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 186 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 186 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (186 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (186 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 186 (MemNextE.MemRE spec mapping 186 (RtSaved.accPA pins mapping (186, 1, 11, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (186, 1, 11, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (186, 1, 11, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_186 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_186 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 186 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_186).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_186

#check "CURRENT_DECL heap mem_step_189"
theorem mem_step_189 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 189 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 189 + 1 ≤ capacity)
    (drawBound : drawsBefore 189 + 1 ≤ drawsBefore (189 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (189, 1, 12, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 189 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 189 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (189 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (189 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 189 (MemNextE.MemRE spec mapping 189 (RtSaved.accPA pins mapping (189, 1, 12, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (189, 1, 12, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (189, 1, 12, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_189 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_189 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 189 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_189).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_189

#check "CURRENT_DECL heap mem_step_192"
theorem mem_step_192 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 192 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 192 + 1 ≤ capacity)
    (drawBound : drawsBefore 192 + 1 ≤ drawsBefore (192 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (192, 1, 13, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 192 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 192 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (192 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (192 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 192 (MemNextE.MemRE spec mapping 192 (RtSaved.accPA pins mapping (192, 1, 13, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (192, 1, 13, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (192, 1, 13, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_192 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_192 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 192 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_192).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_192

#check "CURRENT_DECL heap mem_step_195"
theorem mem_step_195 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 195 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 195 + 1 ≤ capacity)
    (drawBound : drawsBefore 195 + 1 ≤ drawsBefore (195 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (195, 1, 14, 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 195 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 195 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (195 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (195 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 195 (MemNextE.MemRE spec mapping 195 (RtSaved.accPA pins mapping (195, 1, 14, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (195, 1, 14, 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (195, 1, 14, 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_195 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_195 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 195 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_195).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_195

end ReleaseProfile.DefaultHeapBranchRows
