-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapMemRows00
import HeapV2StepCerts.Residue.Step5Mem_00
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap mem_step_11"
theorem mem_step_11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 11 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 11 + 1 ≤ capacity)
    (drawBound : drawsBefore 11 + 1 ≤ drawsBefore (11 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (11, 0, (-16), 16, true)) true 16)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 11 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 11 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (11 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (11 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 11 (MemNextE.MemRE spec mapping 11 (RtSaved.accPA pins mapping (11, 0, (-16), 16, true)) (RtSaved.MemFacts.StpPay pins mapping (11, 0, (-16), 16, true) (19#5) (30#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (11, 0, (-16), 16, true)) true 16)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (11, 0, (-16), 16, true)) true 16)
    (fun x inv => DefaultHeapMemRows.step_11 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_11 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => RtSaved2.field_stp11 (MemNextE.MemRE.toR r).2.2.2.1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 11 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_11).1 rfl) res.1, RtSaved3.field_stp11 (MemNextE.MemRE.toR r).2.2.2.1 res.2⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_11

#check "CURRENT_DECL heap mem_step_18"
theorem mem_step_18 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 18 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 18 + 1 ≤ capacity)
    (drawBound : drawsBefore 18 + 1 ≤ drawsBefore (18 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (18, 2, 0, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 18 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 18 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (18 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (18 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 18 (MemNextE.MemRE spec mapping 18 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (18, 2, 0, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (18, 2, 0, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_18 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_18 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 18 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_18

#check "CURRENT_DECL heap mem_step_19"
theorem mem_step_19 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 19 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 19 + 1 ≤ capacity)
    (drawBound : drawsBefore 19 + 1 ≤ drawsBefore (19 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (19, 0, (-64), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 19 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 19 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (19 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (19 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 19 (MemNextE.MemRE spec mapping 19 (RtSaved.accPA pins mapping (19, 0, (-64), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (19, 0, (-64), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (19, 0, (-64), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_19 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_19 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 19 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_19).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_19

#check "CURRENT_DECL heap mem_step_22"
theorem mem_step_22 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 22 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 22 + 1 ≤ capacity)
    (drawBound : drawsBefore 22 + 1 ≤ drawsBefore (22 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (22, 2, 1, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 22 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 22 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (22 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (22 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 22 (MemNextE.MemRE spec mapping 22 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (22, 2, 1, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (22, 2, 1, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_22 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_22 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 22 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_22

#check "CURRENT_DECL heap mem_step_23"
theorem mem_step_23 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 23 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 23 + 1 ≤ capacity)
    (drawBound : drawsBefore 23 + 1 ≤ drawsBefore (23 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (23, 0, (-63), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 23 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 23 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (23 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (23 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 23 (MemNextE.MemRE spec mapping 23 (RtSaved.accPA pins mapping (23, 0, (-63), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (23, 0, (-63), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (23, 0, (-63), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_23 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_23 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 23 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_23).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_23

#check "CURRENT_DECL heap mem_step_26"
theorem mem_step_26 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 26 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 26 + 1 ≤ capacity)
    (drawBound : drawsBefore 26 + 1 ≤ drawsBefore (26 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (26, 2, 2, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 26 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 26 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (26 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (26 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 26 (MemNextE.MemRE spec mapping 26 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (26, 2, 2, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (26, 2, 2, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_26 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_26 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 26 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_26

#check "CURRENT_DECL heap mem_step_27"
theorem mem_step_27 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 27 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 27 + 1 ≤ capacity)
    (drawBound : drawsBefore 27 + 1 ≤ drawsBefore (27 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (27, 0, (-62), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 27 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 27 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (27 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (27 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 27 (MemNextE.MemRE spec mapping 27 (RtSaved.accPA pins mapping (27, 0, (-62), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (27, 0, (-62), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (27, 0, (-62), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_27 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_27 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 27 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_27).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_27

#check "CURRENT_DECL heap mem_step_30"
theorem mem_step_30 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 30 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 30 + 1 ≤ capacity)
    (drawBound : drawsBefore 30 + 1 ≤ drawsBefore (30 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (30, 2, 3, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 30 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 30 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (30 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (30 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 30 (MemNextE.MemRE spec mapping 30 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (30, 2, 3, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (30, 2, 3, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_30 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_30 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 30 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_30

#check "CURRENT_DECL heap mem_step_31"
theorem mem_step_31 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 31 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 31 + 1 ≤ capacity)
    (drawBound : drawsBefore 31 + 1 ≤ drawsBefore (31 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (31, 0, (-61), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 31 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 31 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (31 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (31 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 31 (MemNextE.MemRE spec mapping 31 (RtSaved.accPA pins mapping (31, 0, (-61), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (31, 0, (-61), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (31, 0, (-61), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_31 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_31 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 31 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_31).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_31

#check "CURRENT_DECL heap mem_step_34"
theorem mem_step_34 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 34 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 34 + 1 ≤ capacity)
    (drawBound : drawsBefore 34 + 1 ≤ drawsBefore (34 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (34, 2, 4, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 34 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 34 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (34 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (34 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 34 (MemNextE.MemRE spec mapping 34 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (34, 2, 4, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (34, 2, 4, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_34 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_34 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 34 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_34

#check "CURRENT_DECL heap mem_step_35"
theorem mem_step_35 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 35 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 35 + 1 ≤ capacity)
    (drawBound : drawsBefore 35 + 1 ≤ drawsBefore (35 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (35, 0, (-60), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 35 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 35 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (35 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (35 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 35 (MemNextE.MemRE spec mapping 35 (RtSaved.accPA pins mapping (35, 0, (-60), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (35, 0, (-60), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (35, 0, (-60), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_35 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_35 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 35 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_35).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_35

#check "CURRENT_DECL heap mem_step_38"
theorem mem_step_38 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 38 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 38 + 1 ≤ capacity)
    (drawBound : drawsBefore 38 + 1 ≤ drawsBefore (38 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (38, 2, 5, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 38 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 38 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (38 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (38 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 38 (MemNextE.MemRE spec mapping 38 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (38, 2, 5, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (38, 2, 5, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_38 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_38 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 38 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_38

#check "CURRENT_DECL heap mem_step_39"
theorem mem_step_39 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 39 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 39 + 1 ≤ capacity)
    (drawBound : drawsBefore 39 + 1 ≤ drawsBefore (39 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (39, 0, (-59), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 39 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 39 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (39 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (39 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 39 (MemNextE.MemRE spec mapping 39 (RtSaved.accPA pins mapping (39, 0, (-59), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (39, 0, (-59), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (39, 0, (-59), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_39 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_39 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 39 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_39).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_39

#check "CURRENT_DECL heap mem_step_42"
theorem mem_step_42 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 42 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 42 + 1 ≤ capacity)
    (drawBound : drawsBefore 42 + 1 ≤ drawsBefore (42 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (42, 2, 6, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 42 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 42 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (42 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (42 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 42 (MemNextE.MemRE spec mapping 42 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (42, 2, 6, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (42, 2, 6, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_42 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_42 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 42 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_42

#check "CURRENT_DECL heap mem_step_43"
theorem mem_step_43 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 43 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 43 + 1 ≤ capacity)
    (drawBound : drawsBefore 43 + 1 ≤ drawsBefore (43 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (43, 0, (-58), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 43 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 43 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (43 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (43 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 43 (MemNextE.MemRE spec mapping 43 (RtSaved.accPA pins mapping (43, 0, (-58), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (43, 0, (-58), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (43, 0, (-58), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_43 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_43 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 43 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_43).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_43

#check "CURRENT_DECL heap mem_step_46"
theorem mem_step_46 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 46 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 46 + 1 ≤ capacity)
    (drawBound : drawsBefore 46 + 1 ≤ drawsBefore (46 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (46, 2, 7, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 46 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 46 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (46 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (46 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 46 (MemNextE.MemRE spec mapping 46 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (46, 2, 7, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (46, 2, 7, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_46 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_46 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 46 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_46

#check "CURRENT_DECL heap mem_step_47"
theorem mem_step_47 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 47 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 47 + 1 ≤ capacity)
    (drawBound : drawsBefore 47 + 1 ≤ drawsBefore (47 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (47, 0, (-57), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 47 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 47 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (47 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (47 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 47 (MemNextE.MemRE spec mapping 47 (RtSaved.accPA pins mapping (47, 0, (-57), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (47, 0, (-57), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (47, 0, (-57), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_47 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_47 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 47 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_47).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_47

#check "CURRENT_DECL heap mem_step_50"
theorem mem_step_50 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 50 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 50 + 1 ≤ capacity)
    (drawBound : drawsBefore 50 + 1 ≤ drawsBefore (50 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (50, 2, 8, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 50 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 50 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (50 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (50 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 50 (MemNextE.MemRE spec mapping 50 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (50, 2, 8, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (50, 2, 8, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_50 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_50 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 50 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_50

#check "CURRENT_DECL heap mem_step_51"
theorem mem_step_51 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 51 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 51 + 1 ≤ capacity)
    (drawBound : drawsBefore 51 + 1 ≤ drawsBefore (51 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (51, 0, (-56), 1, true)) true 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 51 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 51 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (51 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (51 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 51 (MemNextE.MemRE spec mapping 51 (RtSaved.accPA pins mapping (51, 0, (-56), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (51, 0, (-56), 1, true)) true 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (51, 0, (-56), 1, true)) true 1)
    (fun x inv => DefaultHeapMemRows.step_51 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_51 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 51 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 (HeapV2StepCerts.Residue.sub_store (MemSteps.step_51).1 rfl) res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ => RtSaved.accPA_sep sep (by decide +kernel) rfl (by decide) (by decide)) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_51

#check "CURRENT_DECL heap mem_step_54"
theorem mem_step_54 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping))
    (sep : RtSaved.SlotSep pins mapping) (mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n)
    (room : 54 < budget) (page : base.toNat % 4096 = 0)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (statusBound : drawsBefore 54 + 1 ≤ capacity)
    (drawBound : drawsBefore 54 + 1 ≤ drawsBefore (54 + 1)) :
    Step real spec mapping (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (54, 2, 9, 1, false)) false 1)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 54 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 54 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (54 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (54 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 54 (MemNextE.MemRE spec mapping 54 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (54, 2, 9, 1, false)) false 1)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (54, 2, 9, 1, false)) false 1)
    (fun x inv => DefaultHeapMemRows.step_54 real spec config rows mapping base budget pins table catalogue entry capacity drawsBefore static dataStatic
      pinAligned codeD nodup room page statusBound drawBound x inv.body)
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_54 np rb vb (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.1)
    (fun _ _ r field => by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved2.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 field)
    (fun _ _ r => (MemNextE.MemRE.toR r).2.2.2.2) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_mem (HeapV2StepCerts.Residue.frameKeep_ok 54 (by decide)) (MemNextE.MemRE.toR r).1 (MemNextE.MemRE.toR r).2.2.1 HeapV2StepCerts.Residue.sub_false res.1, (by obtain ⟨w, wo, inD⟩ := (MemNextE.MemRE.toR r).2.2.1; exact RtSaved3.carry_mem (by decide) (by decide) (by decide) (by decide) w _ wo inD (fun _ _ _ f => f.elim) (MemNextE.MemRE.toR r).1 res.2)⟩)
    (fun _ _ r => r.2.2.2.2.1) (fun _ _ r => r.2.2.2.2.2.2.1)

#print axioms mem_step_54

end ReleaseProfile.DefaultHeapBranchRows
