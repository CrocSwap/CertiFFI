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

/-- step 135 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_135 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 135 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 135 + 1 ≤ capacity)
    (drawBound : drawsBefore 135 + 1 ≤ drawsBefore (135 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 135)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (135 + 1)) (MemNextE.MemRE spec mapping 135 (RtSaved.accPA pins mapping (135, 0, (-35), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (135, 0, (-35), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 135 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (135, 0, (-35), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_135).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (135, 0, (-35), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_135).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_135).2.1 (MemSteps.step_135).2.2.2 rfl rfl (MemSteps.step_135).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 135 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 135 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 138 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_138 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 138 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 138 + 1 ≤ capacity)
    (drawBound : drawsBefore 138 + 1 ≤ drawsBefore (138 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 138)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (138 + 1)) (MemNextE.MemRE spec mapping 138 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (138, 2, 30, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 138 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (138, 2, 30, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_138).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_138).2.1 (MemSteps.step_138).2.2.2 rfl rfl (MemSteps.step_138).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 138 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 138 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 139 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_139 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 139 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 139 + 1 ≤ capacity)
    (drawBound : drawsBefore 139 + 1 ≤ drawsBefore (139 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 139)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (139 + 1)) (MemNextE.MemRE spec mapping 139 (RtSaved.accPA pins mapping (139, 0, (-34), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (139, 0, (-34), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 139 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (139, 0, (-34), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_139).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (139, 0, (-34), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_139).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_139).2.1 (MemSteps.step_139).2.2.2 rfl rfl (MemSteps.step_139).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 139 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 139 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 142 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_142 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 142 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 142 + 1 ≤ capacity)
    (drawBound : drawsBefore 142 + 1 ≤ drawsBefore (142 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 142)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (142 + 1)) (MemNextE.MemRE spec mapping 142 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (142, 2, 31, 1, false)) false 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 142 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (142, 2, 31, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_142).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_142).2.1 (MemSteps.step_142).2.2.2 rfl rfl (MemSteps.step_142).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 142 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 142 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 143 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_143 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 143 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 143 + 1 ≤ capacity)
    (drawBound : drawsBefore 143 + 1 ≤ drawsBefore (143 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 143)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (143 + 1)) (MemNextE.MemRE spec mapping 143 (RtSaved.accPA pins mapping (143, 0, (-33), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (143, 0, (-33), 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 143 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (143, 0, (-33), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_143).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (143, 0, (-33), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_143).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_143).2.1 (MemSteps.step_143).2.2.2 rfl rfl (MemSteps.step_143).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 143 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 143 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 153 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_153 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 153 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 153 + 1 ≤ capacity)
    (drawBound : drawsBefore 153 + 1 ≤ drawsBefore (153 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 153)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (153 + 1)) (MemNextE.MemRE spec mapping 153 (RtSaved.accPA pins mapping (153, 1, 0, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (153, 1, 0, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 153 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (153, 1, 0, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_153).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (153, 1, 0, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_153).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_153).2.1 (MemSteps.step_153).2.2.2 rfl rfl (MemSteps.step_153).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 153 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 153 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 156 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_156 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 156 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 156 + 1 ≤ capacity)
    (drawBound : drawsBefore 156 + 1 ≤ drawsBefore (156 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 156)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (156 + 1)) (MemNextE.MemRE spec mapping 156 (RtSaved.accPA pins mapping (156, 1, 1, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (156, 1, 1, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 156 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (156, 1, 1, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_156).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (156, 1, 1, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_156).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_156).2.1 (MemSteps.step_156).2.2.2 rfl rfl (MemSteps.step_156).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 156 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 156 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 159 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_159 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 159 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 159 + 1 ≤ capacity)
    (drawBound : drawsBefore 159 + 1 ≤ drawsBefore (159 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 159)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (159 + 1)) (MemNextE.MemRE spec mapping 159 (RtSaved.accPA pins mapping (159, 1, 2, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (159, 1, 2, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 159 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (159, 1, 2, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_159).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (159, 1, 2, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_159).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_159).2.1 (MemSteps.step_159).2.2.2 rfl rfl (MemSteps.step_159).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 159 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 159 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 162 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_162 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 162 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 162 + 1 ≤ capacity)
    (drawBound : drawsBefore 162 + 1 ≤ drawsBefore (162 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 162)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (162 + 1)) (MemNextE.MemRE spec mapping 162 (RtSaved.accPA pins mapping (162, 1, 3, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (162, 1, 3, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 162 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (162, 1, 3, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_162).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (162, 1, 3, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_162).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_162).2.1 (MemSteps.step_162).2.2.2 rfl rfl (MemSteps.step_162).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 162 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 162 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 165 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_165 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 165 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 165 + 1 ≤ capacity)
    (drawBound : drawsBefore 165 + 1 ≤ drawsBefore (165 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 165)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (165 + 1)) (MemNextE.MemRE spec mapping 165 (RtSaved.accPA pins mapping (165, 1, 4, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (165, 1, 4, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 165 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (165, 1, 4, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_165).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (165, 1, 4, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_165).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_165).2.1 (MemSteps.step_165).2.2.2 rfl rfl (MemSteps.step_165).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 165 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 165 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 168 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_168 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 168 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 168 + 1 ≤ capacity)
    (drawBound : drawsBefore 168 + 1 ≤ drawsBefore (168 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 168)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (168 + 1)) (MemNextE.MemRE spec mapping 168 (RtSaved.accPA pins mapping (168, 1, 5, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (168, 1, 5, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 168 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (168, 1, 5, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_168).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (168, 1, 5, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_168).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_168).2.1 (MemSteps.step_168).2.2.2 rfl rfl (MemSteps.step_168).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 168 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 168 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 171 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_171 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 171 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 171 + 1 ≤ capacity)
    (drawBound : drawsBefore 171 + 1 ≤ drawsBefore (171 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 171)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (171 + 1)) (MemNextE.MemRE spec mapping 171 (RtSaved.accPA pins mapping (171, 1, 6, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (171, 1, 6, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 171 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (171, 1, 6, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_171).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (171, 1, 6, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_171).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_171).2.1 (MemSteps.step_171).2.2.2 rfl rfl (MemSteps.step_171).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 171 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 171 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 174 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_174 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 174 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 174 + 1 ≤ capacity)
    (drawBound : drawsBefore 174 + 1 ≤ drawsBefore (174 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 174)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (174 + 1)) (MemNextE.MemRE spec mapping 174 (RtSaved.accPA pins mapping (174, 1, 7, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (174, 1, 7, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 174 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (174, 1, 7, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_174).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (174, 1, 7, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_174).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_174).2.1 (MemSteps.step_174).2.2.2 rfl rfl (MemSteps.step_174).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 174 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 174 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 177 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_177 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 177 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 177 + 1 ≤ capacity)
    (drawBound : drawsBefore 177 + 1 ≤ drawsBefore (177 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 177)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (177 + 1)) (MemNextE.MemRE spec mapping 177 (RtSaved.accPA pins mapping (177, 1, 8, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (177, 1, 8, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 177 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (177, 1, 8, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_177).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (177, 1, 8, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_177).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_177).2.1 (MemSteps.step_177).2.2.2 rfl rfl (MemSteps.step_177).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 177 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 177 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 180 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_180 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 180 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 180 + 1 ≤ capacity)
    (drawBound : drawsBefore 180 + 1 ≤ drawsBefore (180 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 180)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (180 + 1)) (MemNextE.MemRE spec mapping 180 (RtSaved.accPA pins mapping (180, 1, 9, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (180, 1, 9, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 180 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (180, 1, 9, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_180).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (180, 1, 9, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_180).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_180).2.1 (MemSteps.step_180).2.2.2 rfl rfl (MemSteps.step_180).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 180 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 180 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 183 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_183 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 183 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 183 + 1 ≤ capacity)
    (drawBound : drawsBefore 183 + 1 ≤ drawsBefore (183 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 183)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (183 + 1)) (MemNextE.MemRE spec mapping 183 (RtSaved.accPA pins mapping (183, 1, 10, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (183, 1, 10, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 183 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (183, 1, 10, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_183).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (183, 1, 10, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_183).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_183).2.1 (MemSteps.step_183).2.2.2 rfl rfl (MemSteps.step_183).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 183 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 183 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 186 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_186 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 186 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 186 + 1 ≤ capacity)
    (drawBound : drawsBefore 186 + 1 ≤ drawsBefore (186 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 186)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (186 + 1)) (MemNextE.MemRE spec mapping 186 (RtSaved.accPA pins mapping (186, 1, 11, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (186, 1, 11, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 186 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (186, 1, 11, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_186).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (186, 1, 11, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_186).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_186).2.1 (MemSteps.step_186).2.2.2 rfl rfl (MemSteps.step_186).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 186 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 186 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 189 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_189 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 189 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 189 + 1 ≤ capacity)
    (drawBound : drawsBefore 189 + 1 ≤ drawsBefore (189 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 189)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (189 + 1)) (MemNextE.MemRE spec mapping 189 (RtSaved.accPA pins mapping (189, 1, 12, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (189, 1, 12, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 189 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (189, 1, 12, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_189).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (189, 1, 12, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_189).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_189).2.1 (MemSteps.step_189).2.2.2 rfl rfl (MemSteps.step_189).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 189 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 189 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 192 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_192 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 192 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 192 + 1 ≤ capacity)
    (drawBound : drawsBefore 192 + 1 ≤ drawsBefore (192 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 192)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (192 + 1)) (MemNextE.MemRE spec mapping 192 (RtSaved.accPA pins mapping (192, 1, 13, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (192, 1, 13, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 192 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (192, 1, 13, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_192).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (192, 1, 13, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_192).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_192).2.1 (MemSteps.step_192).2.2.2 rfl rfl (MemSteps.step_192).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 192 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 192 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

/-- step 195 @+0x180 STRB_post 38001461 (Strb {'Rt': 1, 'Rn': 3, 'imm9': 1}) -/
theorem step_195 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 195 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 195 + 1 ≤ capacity)
    (drawBound : drawsBefore 195 + 1 ≤ drawsBefore (195 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 195)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (195 + 1)) (MemNextE.MemRE spec mapping 195 (RtSaved.accPA pins mapping (195, 1, 14, 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (195, 1, 14, 1, true)) true 1)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 195 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (195, 1, 14, 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_195).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (195, 1, 14, 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_195).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_195).2.1 (MemSteps.step_195).2.2.2 rfl rfl (MemSteps.step_195).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 195 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 195 pins table catalogue static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.core)

end ReleaseProfile.DefaultHeapMemRows
