-- Generated from the signed heap-v2 memory rows by gen_heap_memory.py.
import DefaultHeapMemFacts
import DefaultHeapMemoryDit
import DefaultHeapCode
import DefaultHeapSavedMemFacts

open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapMemDitRows

/-- step 198 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_198 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 198 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 198 + 1 ≤ capacity)
    (drawBound : drawsBefore 198 + 1 ≤ drawsBefore (198 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 198)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (198 + 1)) (fun s f => (MemNextE.MemRE spec mapping 198 (RtSaved.accPA pins mapping (198, 1, 15, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (198, 1, 15, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 198 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (198, 1, 15, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_198).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (198, 1, 15, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_198).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_198).2.1 (MemSteps.step_198).2.2.2 rfl rfl (MemSteps.step_198).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 198 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 198 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_198

/-- step 201 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_201 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 201 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 201 + 1 ≤ capacity)
    (drawBound : drawsBefore 201 + 1 ≤ drawsBefore (201 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 201)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (201 + 1)) (fun s f => (MemNextE.MemRE spec mapping 201 (RtSaved.accPA pins mapping (201, 1, 16, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (201, 1, 16, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 201 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (201, 1, 16, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_201).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (201, 1, 16, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_201).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_201).2.1 (MemSteps.step_201).2.2.2 rfl rfl (MemSteps.step_201).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 201 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 201 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_201

/-- step 204 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_204 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 204 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 204 + 1 ≤ capacity)
    (drawBound : drawsBefore 204 + 1 ≤ drawsBefore (204 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 204)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (204 + 1)) (fun s f => (MemNextE.MemRE spec mapping 204 (RtSaved.accPA pins mapping (204, 1, 17, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (204, 1, 17, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 204 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (204, 1, 17, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_204).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (204, 1, 17, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_204).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_204).2.1 (MemSteps.step_204).2.2.2 rfl rfl (MemSteps.step_204).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 204 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 204 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_204

/-- step 207 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_207 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 207 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 207 + 1 ≤ capacity)
    (drawBound : drawsBefore 207 + 1 ≤ drawsBefore (207 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 207)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (207 + 1)) (fun s f => (MemNextE.MemRE spec mapping 207 (RtSaved.accPA pins mapping (207, 1, 18, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (207, 1, 18, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 207 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (207, 1, 18, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_207).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (207, 1, 18, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_207).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_207).2.1 (MemSteps.step_207).2.2.2 rfl rfl (MemSteps.step_207).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 207 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 207 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_207

/-- step 210 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_210 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 210 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 210 + 1 ≤ capacity)
    (drawBound : drawsBefore 210 + 1 ≤ drawsBefore (210 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 210)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (210 + 1)) (fun s f => (MemNextE.MemRE spec mapping 210 (RtSaved.accPA pins mapping (210, 1, 19, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (210, 1, 19, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 210 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (210, 1, 19, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_210).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (210, 1, 19, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_210).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_210).2.1 (MemSteps.step_210).2.2.2 rfl rfl (MemSteps.step_210).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 210 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 210 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_210

/-- step 213 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_213 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 213 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 213 + 1 ≤ capacity)
    (drawBound : drawsBefore 213 + 1 ≤ drawsBefore (213 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 213)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (213 + 1)) (fun s f => (MemNextE.MemRE spec mapping 213 (RtSaved.accPA pins mapping (213, 1, 20, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (213, 1, 20, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 213 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (213, 1, 20, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_213).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (213, 1, 20, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_213).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_213).2.1 (MemSteps.step_213).2.2.2 rfl rfl (MemSteps.step_213).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 213 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 213 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_213

/-- step 216 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_216 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 216 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 216 + 1 ≤ capacity)
    (drawBound : drawsBefore 216 + 1 ≤ drawsBefore (216 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 216)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (216 + 1)) (fun s f => (MemNextE.MemRE spec mapping 216 (RtSaved.accPA pins mapping (216, 1, 21, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (216, 1, 21, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 216 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (216, 1, 21, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_216).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (216, 1, 21, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_216).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_216).2.1 (MemSteps.step_216).2.2.2 rfl rfl (MemSteps.step_216).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 216 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 216 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_216

/-- step 219 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_219 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 219 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 219 + 1 ≤ capacity)
    (drawBound : drawsBefore 219 + 1 ≤ drawsBefore (219 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 219)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (219 + 1)) (fun s f => (MemNextE.MemRE spec mapping 219 (RtSaved.accPA pins mapping (219, 1, 22, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (219, 1, 22, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 219 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (219, 1, 22, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_219).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (219, 1, 22, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_219).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_219).2.1 (MemSteps.step_219).2.2.2 rfl rfl (MemSteps.step_219).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 219 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 219 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_219

/-- step 222 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_222 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 222 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 222 + 1 ≤ capacity)
    (drawBound : drawsBefore 222 + 1 ≤ drawsBefore (222 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 222)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (222 + 1)) (fun s f => (MemNextE.MemRE spec mapping 222 (RtSaved.accPA pins mapping (222, 1, 23, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (222, 1, 23, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 222 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (222, 1, 23, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_222).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (222, 1, 23, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_222).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_222).2.1 (MemSteps.step_222).2.2.2 rfl rfl (MemSteps.step_222).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 222 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 222 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_222

/-- step 225 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_225 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 225 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 225 + 1 ≤ capacity)
    (drawBound : drawsBefore 225 + 1 ≤ drawsBefore (225 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 225)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (225 + 1)) (fun s f => (MemNextE.MemRE spec mapping 225 (RtSaved.accPA pins mapping (225, 1, 24, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (225, 1, 24, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 225 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (225, 1, 24, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_225).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (225, 1, 24, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_225).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_225).2.1 (MemSteps.step_225).2.2.2 rfl rfl (MemSteps.step_225).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 225 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 225 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_225

/-- step 228 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_228 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 228 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 228 + 1 ≤ capacity)
    (drawBound : drawsBefore 228 + 1 ≤ drawsBefore (228 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 228)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (228 + 1)) (fun s f => (MemNextE.MemRE spec mapping 228 (RtSaved.accPA pins mapping (228, 1, 25, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (228, 1, 25, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 228 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (228, 1, 25, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_228).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (228, 1, 25, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_228).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_228).2.1 (MemSteps.step_228).2.2.2 rfl rfl (MemSteps.step_228).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 228 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 228 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_228

/-- step 231 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_231 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 231 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 231 + 1 ≤ capacity)
    (drawBound : drawsBefore 231 + 1 ≤ drawsBefore (231 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 231)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (231 + 1)) (fun s f => (MemNextE.MemRE spec mapping 231 (RtSaved.accPA pins mapping (231, 1, 26, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (231, 1, 26, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 231 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (231, 1, 26, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_231).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (231, 1, 26, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_231).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_231).2.1 (MemSteps.step_231).2.2.2 rfl rfl (MemSteps.step_231).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 231 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 231 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_231

/-- step 234 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_234 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 234 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 234 + 1 ≤ capacity)
    (drawBound : drawsBefore 234 + 1 ≤ drawsBefore (234 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 234)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (234 + 1)) (fun s f => (MemNextE.MemRE spec mapping 234 (RtSaved.accPA pins mapping (234, 1, 27, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (234, 1, 27, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 234 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (234, 1, 27, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_234).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (234, 1, 27, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_234).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_234).2.1 (MemSteps.step_234).2.2.2 rfl rfl (MemSteps.step_234).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 234 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 234 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_234

/-- step 237 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_237 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 237 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 237 + 1 ≤ capacity)
    (drawBound : drawsBefore 237 + 1 ≤ drawsBefore (237 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 237)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (237 + 1)) (fun s f => (MemNextE.MemRE spec mapping 237 (RtSaved.accPA pins mapping (237, 1, 28, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (237, 1, 28, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 237 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (237, 1, 28, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_237).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (237, 1, 28, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_237).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_237).2.1 (MemSteps.step_237).2.2.2 rfl rfl (MemSteps.step_237).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 237 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 237 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_237

/-- step 240 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_240 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 240 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 240 + 1 ≤ capacity)
    (drawBound : drawsBefore 240 + 1 ≤ drawsBefore (240 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 240)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (240 + 1)) (fun s f => (MemNextE.MemRE spec mapping 240 (RtSaved.accPA pins mapping (240, 1, 29, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (240, 1, 29, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 240 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (240, 1, 29, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_240).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (240, 1, 29, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_240).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_240).2.1 (MemSteps.step_240).2.2.2 rfl rfl (MemSteps.step_240).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 240 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 240 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_240

/-- step 243 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_243 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 243 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 243 + 1 ≤ capacity)
    (drawBound : drawsBefore 243 + 1 ≤ drawsBefore (243 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 243)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (243 + 1)) (fun s f => (MemNextE.MemRE spec mapping 243 (RtSaved.accPA pins mapping (243, 1, 30, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (243, 1, 30, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 243 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (243, 1, 30, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_243).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (243, 1, 30, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_243).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_243).2.1 (MemSteps.step_243).2.2.2 rfl rfl (MemSteps.step_243).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 243 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 243 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_243

/-- step 246 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_246 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 246 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 246 + 1 ≤ capacity)
    (drawBound : drawsBefore 246 + 1 ≤ drawsBefore (246 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 246)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (246 + 1)) (fun s f => (MemNextE.MemRE spec mapping 246 (RtSaved.accPA pins mapping (246, 1, 31, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (246, 1, 31, 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 246 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (246, 1, 31, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_246).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (246, 1, 31, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_246).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_246).2.1 (MemSteps.step_246).2.2.2 rfl rfl (MemSteps.step_246).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 246 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 246 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_246

/-- step 253 @+0x190 LDP64_off a9400c22 (Ldp8 {'Rt': 2, 'Rn': 1, 'Rt2': 3, 'imm7': 0, '_pair_dispatch': True}) -/
theorem step_253 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 253 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 253 + 2 ≤ capacity)
    (drawBound : drawsBefore 253 + 2 ≤ drawsBefore (253 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 253)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (253 + 1)) (fun s f => (MemNextE.MemRE spec mapping 253 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (253, 0, (-64), 16, false)) false 16)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 253 catalogue entry capacity drawsBefore 2 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (253, 0, (-64), 16, false)) false 16) nodup
    (NativeEntryBodyDispatch.Ldp8.selected (2#5) (1#5) (3#5) (0#7)) NativeEntryBodyMem.Ldp8.writes 611
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldp8 real spec config rows mapping dataStatic pinAligned (MemSteps.step_253).1 rfl (0#7) (1#5) (2#5) (3#5) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_253).2.1 (MemSteps.step_253).2.2.2.1 ⟨(MemSteps.step_253).2.2.2.2.1, (MemSteps.step_253).2.2.2.2.2.1⟩ (MemSteps.step_253).2.2.2.2.2.2 rfl rfl (MemSteps.step_253).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 253 pins table catalogue static 0x190 0xa9400c22
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 253 pins table catalogue static 0x190 0xa9400c22
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldp8.selected (2#5) (1#5) (3#5) (0#7)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_253

/-- step 256 @+0x19c LDP64_off a9411424 (Ldp8 {'Rt': 4, 'Rn': 1, 'Rt2': 5, 'imm7': 2, '_pair_dispatch': True}) -/
theorem step_256 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 256 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 256 + 2 ≤ capacity)
    (drawBound : drawsBefore 256 + 2 ≤ drawsBefore (256 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 256)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (256 + 1)) (fun s f => (MemNextE.MemRE spec mapping 256 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (256, 0, (-48), 16, false)) false 16)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 256 catalogue entry capacity drawsBefore 2 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (256, 0, (-48), 16, false)) false 16) nodup
    (NativeEntryBodyDispatch.Ldp8.selected (4#5) (1#5) (5#5) (2#7)) NativeEntryBodyMem.Ldp8.writes 611
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldp8 real spec config rows mapping dataStatic pinAligned (MemSteps.step_256).1 rfl (2#7) (1#5) (4#5) (5#5) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_256).2.1 (MemSteps.step_256).2.2.2.1 ⟨(MemSteps.step_256).2.2.2.2.1, (MemSteps.step_256).2.2.2.2.2.1⟩ (MemSteps.step_256).2.2.2.2.2.2 rfl rfl (MemSteps.step_256).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 256 pins table catalogue static 0x19c 0xa9411424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 256 pins table catalogue static 0x19c 0xa9411424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldp8.selected (4#5) (1#5) (5#5) (2#7)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_256

/-- step 329 @+0x2c0 STP64_off a9002408 (Stp8 {'Rt': 8, 'Rn': 0, 'Rt2': 9, 'imm7': 0, '_pair_dispatch': True}) -/
theorem step_329 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 329 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 329 + 2 ≤ capacity)
    (drawBound : drawsBefore 329 + 2 ≤ drawsBefore (329 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 329)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (329 + 1)) (fun s f => (MemNextE.MemRE spec mapping 329 (RtSaved.accPA pins mapping (329, 1, 0, 16, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (329, 1, 0, 16, true)) true 16)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 329 catalogue entry capacity drawsBefore 2 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (329, 1, 0, 16, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_329).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (329, 1, 0, 16, true)) true 16) nodup
    (NativeEntryBodyDispatch.Stp8.selected (8#5) (0#5) (9#5) (0#7)) NativeEntryBodyMem.Stp8.writes 617
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Stp8 real spec config rows mapping dataStatic pinAligned (MemSteps.step_329).1 rfl (0#7) (0#5) (8#5) (9#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_329).2.1 (MemSteps.step_329).2.2.2.1 ⟨(MemSteps.step_329).2.2.2.2.1, (MemSteps.step_329).2.2.2.2.2.1⟩ (MemSteps.step_329).2.2.2.2.2.2 rfl rfl (MemSteps.step_329).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 329 pins table catalogue static 0x2c0 0xa9002408
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 329 pins table catalogue static 0x2c0 0xa9002408
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp8.selected (8#5) (0#5) (9#5) (0#7)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_329

end ReleaseProfile.DefaultHeapMemDitRows
