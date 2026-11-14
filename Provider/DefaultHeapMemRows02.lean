-- Generated from the signed heap-v2 memory rows by gen_heap_memory.py.
import DefaultHeapMemFacts
import DefaultHeapCode
import DefaultHeapSavedMemFacts

open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapMemRows

/-- step 95 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_95 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 95 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 95 + 1 ≤ capacity)
    (drawBound : drawsBefore 95 + 1 ≤ drawsBefore (95 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 95)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (95 + 1)) (MemNextE.MemRE spec mapping 95 (RtSaved.accPA pins mapping (95, 0, (-45), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (95, 0, (-45), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 95 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (95, 0, (-45), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_95).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (95, 0, (-45), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_95).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_95).2.1 (MemSteps.step_95).2.2.2 rfl rfl (MemSteps.step_95).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 95 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 95 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 98 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_98 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 98 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 98 + 1 ≤ capacity)
    (drawBound : drawsBefore 98 + 1 ≤ drawsBefore (98 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 98)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (98 + 1)) (MemNextE.MemRE spec mapping 98 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (98, 2, 20, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 98 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (98, 2, 20, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_98).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_98).2.1 (MemSteps.step_98).2.2.2 rfl rfl (MemSteps.step_98).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 98 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 98 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 99 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_99 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 99 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 99 + 1 ≤ capacity)
    (drawBound : drawsBefore 99 + 1 ≤ drawsBefore (99 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 99)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (99 + 1)) (MemNextE.MemRE spec mapping 99 (RtSaved.accPA pins mapping (99, 0, (-44), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (99, 0, (-44), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 99 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (99, 0, (-44), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_99).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (99, 0, (-44), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_99).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_99).2.1 (MemSteps.step_99).2.2.2 rfl rfl (MemSteps.step_99).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 99 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 99 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 102 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_102 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 102 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 102 + 1 ≤ capacity)
    (drawBound : drawsBefore 102 + 1 ≤ drawsBefore (102 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 102)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (102 + 1)) (MemNextE.MemRE spec mapping 102 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (102, 2, 21, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 102 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (102, 2, 21, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_102).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_102).2.1 (MemSteps.step_102).2.2.2 rfl rfl (MemSteps.step_102).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 102 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 102 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 103 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_103 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 103 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 103 + 1 ≤ capacity)
    (drawBound : drawsBefore 103 + 1 ≤ drawsBefore (103 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 103)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (103 + 1)) (MemNextE.MemRE spec mapping 103 (RtSaved.accPA pins mapping (103, 0, (-43), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (103, 0, (-43), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 103 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (103, 0, (-43), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_103).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (103, 0, (-43), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_103).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_103).2.1 (MemSteps.step_103).2.2.2 rfl rfl (MemSteps.step_103).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 103 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 103 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 106 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_106 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 106 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 106 + 1 ≤ capacity)
    (drawBound : drawsBefore 106 + 1 ≤ drawsBefore (106 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 106)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (106 + 1)) (MemNextE.MemRE spec mapping 106 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (106, 2, 22, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 106 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (106, 2, 22, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_106).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_106).2.1 (MemSteps.step_106).2.2.2 rfl rfl (MemSteps.step_106).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 106 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 106 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 107 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_107 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 107 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 107 + 1 ≤ capacity)
    (drawBound : drawsBefore 107 + 1 ≤ drawsBefore (107 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 107)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (107 + 1)) (MemNextE.MemRE spec mapping 107 (RtSaved.accPA pins mapping (107, 0, (-42), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (107, 0, (-42), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 107 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (107, 0, (-42), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_107).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (107, 0, (-42), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_107).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_107).2.1 (MemSteps.step_107).2.2.2 rfl rfl (MemSteps.step_107).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 107 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 107 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 110 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_110 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 110 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 110 + 1 ≤ capacity)
    (drawBound : drawsBefore 110 + 1 ≤ drawsBefore (110 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 110)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (110 + 1)) (MemNextE.MemRE spec mapping 110 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (110, 2, 23, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 110 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (110, 2, 23, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_110).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_110).2.1 (MemSteps.step_110).2.2.2 rfl rfl (MemSteps.step_110).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 110 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 110 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 111 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_111 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 111 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 111 + 1 ≤ capacity)
    (drawBound : drawsBefore 111 + 1 ≤ drawsBefore (111 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 111)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (111 + 1)) (MemNextE.MemRE spec mapping 111 (RtSaved.accPA pins mapping (111, 0, (-41), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (111, 0, (-41), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 111 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (111, 0, (-41), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_111).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (111, 0, (-41), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_111).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_111).2.1 (MemSteps.step_111).2.2.2 rfl rfl (MemSteps.step_111).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 111 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 111 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 114 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_114 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 114 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 114 + 1 ≤ capacity)
    (drawBound : drawsBefore 114 + 1 ≤ drawsBefore (114 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 114)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (114 + 1)) (MemNextE.MemRE spec mapping 114 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (114, 2, 24, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 114 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (114, 2, 24, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_114).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_114).2.1 (MemSteps.step_114).2.2.2 rfl rfl (MemSteps.step_114).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 114 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 114 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 115 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_115 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 115 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 115 + 1 ≤ capacity)
    (drawBound : drawsBefore 115 + 1 ≤ drawsBefore (115 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 115)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (115 + 1)) (MemNextE.MemRE spec mapping 115 (RtSaved.accPA pins mapping (115, 0, (-40), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (115, 0, (-40), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 115 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (115, 0, (-40), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_115).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (115, 0, (-40), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_115).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_115).2.1 (MemSteps.step_115).2.2.2 rfl rfl (MemSteps.step_115).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 115 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 115 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 118 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_118 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 118 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 118 + 1 ≤ capacity)
    (drawBound : drawsBefore 118 + 1 ≤ drawsBefore (118 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 118)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (118 + 1)) (MemNextE.MemRE spec mapping 118 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (118, 2, 25, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 118 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (118, 2, 25, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_118).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_118).2.1 (MemSteps.step_118).2.2.2 rfl rfl (MemSteps.step_118).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 118 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 118 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 119 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_119 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 119 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 119 + 1 ≤ capacity)
    (drawBound : drawsBefore 119 + 1 ≤ drawsBefore (119 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 119)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (119 + 1)) (MemNextE.MemRE spec mapping 119 (RtSaved.accPA pins mapping (119, 0, (-39), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (119, 0, (-39), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 119 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (119, 0, (-39), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_119).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (119, 0, (-39), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_119).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_119).2.1 (MemSteps.step_119).2.2.2 rfl rfl (MemSteps.step_119).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 119 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 119 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 122 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_122 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 122 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 122 + 1 ≤ capacity)
    (drawBound : drawsBefore 122 + 1 ≤ drawsBefore (122 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 122)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (122 + 1)) (MemNextE.MemRE spec mapping 122 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (122, 2, 26, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 122 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (122, 2, 26, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_122).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_122).2.1 (MemSteps.step_122).2.2.2 rfl rfl (MemSteps.step_122).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 122 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 122 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 123 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_123 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 123 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 123 + 1 ≤ capacity)
    (drawBound : drawsBefore 123 + 1 ≤ drawsBefore (123 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 123)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (123 + 1)) (MemNextE.MemRE spec mapping 123 (RtSaved.accPA pins mapping (123, 0, (-38), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (123, 0, (-38), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 123 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (123, 0, (-38), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_123).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (123, 0, (-38), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_123).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_123).2.1 (MemSteps.step_123).2.2.2 rfl rfl (MemSteps.step_123).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 123 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 123 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 126 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_126 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 126 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 126 + 1 ≤ capacity)
    (drawBound : drawsBefore 126 + 1 ≤ drawsBefore (126 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 126)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (126 + 1)) (MemNextE.MemRE spec mapping 126 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (126, 2, 27, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 126 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (126, 2, 27, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_126).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_126).2.1 (MemSteps.step_126).2.2.2 rfl rfl (MemSteps.step_126).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 126 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 126 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 127 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_127 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 127 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 127 + 1 ≤ capacity)
    (drawBound : drawsBefore 127 + 1 ≤ drawsBefore (127 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 127)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (127 + 1)) (MemNextE.MemRE spec mapping 127 (RtSaved.accPA pins mapping (127, 0, (-37), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (127, 0, (-37), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 127 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (127, 0, (-37), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_127).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (127, 0, (-37), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_127).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_127).2.1 (MemSteps.step_127).2.2.2 rfl rfl (MemSteps.step_127).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 127 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 127 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 130 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_130 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 130 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 130 + 1 ≤ capacity)
    (drawBound : drawsBefore 130 + 1 ≤ drawsBefore (130 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 130)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (130 + 1)) (MemNextE.MemRE spec mapping 130 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (130, 2, 28, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 130 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (130, 2, 28, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_130).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_130).2.1 (MemSteps.step_130).2.2.2 rfl rfl (MemSteps.step_130).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 130 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 130 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 131 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_131 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 131 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 131 + 1 ≤ capacity)
    (drawBound : drawsBefore 131 + 1 ≤ drawsBefore (131 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 131)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (131 + 1)) (MemNextE.MemRE spec mapping 131 (RtSaved.accPA pins mapping (131, 0, (-36), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (131, 0, (-36), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 131 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (131, 0, (-36), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_131).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (131, 0, (-36), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_131).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_131).2.1 (MemSteps.step_131).2.2.2 rfl rfl (MemSteps.step_131).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 131 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 131 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 134 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_134 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 134 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 134 + 1 ≤ capacity)
    (drawBound : drawsBefore 134 + 1 ≤ drawsBefore (134 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 134)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (134 + 1)) (MemNextE.MemRE spec mapping 134 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (134, 2, 29, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 134 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (134, 2, 29, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_134).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_134).2.1 (MemSteps.step_134).2.2.2 rfl rfl (MemSteps.step_134).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 134 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 134 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

end ReleaseProfile.DefaultHeapMemRows
