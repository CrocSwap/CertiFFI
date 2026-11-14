-- Generated from the signed heap-v2 memory rows by gen_heap_memory.py.
import DefaultHeapValueMemFacts
import DefaultHeapCode
import DefaultHeapValueMemFacts

open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapValueMemRows

/-- step 330 @+0x2c4 STP64_off a9012c0a (Stp8 {'Rt': 10, 'Rn': 0, 'Rt2': 11, 'imm7': 2, '_pair_dispatch': True}) -/
theorem step_330 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 330 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 330 + 2 ≤ capacity)
    (drawBound : drawsBefore 330 + 2 ≤ drawsBefore (330 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 330)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (330 + 1)) (MemNextE.MemRE spec mapping 330 (RtSaved.accPA pins mapping (330, 1, 16, 16, true)) (RtSaved.MemFacts.StpPay pins mapping (330, 1, 16, 16, true) (10#5) (11#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (330, 1, 16, 16, true)) true 16)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 330 catalogue entry capacity drawsBefore 2 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (330, 1, 16, 16, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_330).1) codeD) (RtSaved.MemFacts.StpPay pins mapping (330, 1, 16, 16, true) (10#5) (11#5)) (fun _ _ _ g _ h => RtSaved.MemFacts.StpPay.transport g h) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (330, 1, 16, 16, true)) true 16) nodup
    (NativeEntryBodyDispatch.Stp8.selected (10#5) (0#5) (11#5) (2#7)) NativeEntryBodyMem.Stp8.writes 617
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapValueMemFacts.memEV_Stp8 real spec config rows mapping dataStatic pinAligned (MemSteps.step_330).1 rfl (2#7) (0#5) (10#5) (11#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_330).2.1 (MemSteps.step_330).2.2.2.1 ⟨(MemSteps.step_330).2.2.2.2.1, (MemSteps.step_330).2.2.2.2.2.1⟩ (MemSteps.step_330).2.2.2.2.2.2 rfl rfl (MemSteps.step_330).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 330 pins table catalogue static 0x2c4 0xa9012c0a
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 330 pins table catalogue static 0x2c4 0xa9012c0a
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp8.selected (10#5) (0#5) (11#5) (2#7)) (by decide +kernel) x inv.core)

/-- step 351 @+0xa8 STP64_off a9000be1 (Stp {'Rt': 1, 'Rn': 31, 'Rt2': 2, 'imm7': 0}) -/
theorem step_351 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 351 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 351 + 1 ≤ capacity)
    (drawBound : drawsBefore 351 + 1 ≤ drawsBefore (351 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 351)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (351 + 1)) (MemNextE.MemRE spec mapping 351 (RtSaved.accPA pins mapping (351, 0, (-64), 16, true)) (RtSaved.MemFacts.StpPay pins mapping (351, 0, (-64), 16, true) (1#5) (2#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (351, 0, (-64), 16, true)) true 16)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 351 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (351, 0, (-64), 16, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_351).1) codeD) (RtSaved.MemFacts.StpPay pins mapping (351, 0, (-64), 16, true) (1#5) (2#5)) (fun _ _ _ g _ h => RtSaved.MemFacts.StpPay.transport g h) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (351, 0, (-64), 16, true)) true 16) nodup
    (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (0#7)) NativeEntryBodyMem.Stp.writes 617
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapValueMemFacts.memEV_Stp real spec config rows mapping dataStatic pinAligned (MemSteps.step_351).1 rfl (0#7) (1#5) (2#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_351).2.1 (MemSteps.step_351).2.2.2.1 (MemSteps.step_351).2.2.2.2 rfl rfl (MemSteps.step_351).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 351 pins table catalogue static 0xa8 0xa9000be1
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 351 pins table catalogue static 0xa8 0xa9000be1
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (0#7)) (by decide +kernel) x inv.core)

/-- step 352 @+0xac STP64_off a9010be1 (Stp {'Rt': 1, 'Rn': 31, 'Rt2': 2, 'imm7': 2}) -/
theorem step_352 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 352 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 352 + 1 ≤ capacity)
    (drawBound : drawsBefore 352 + 1 ≤ drawsBefore (352 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 352)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (352 + 1)) (MemNextE.MemRE spec mapping 352 (RtSaved.accPA pins mapping (352, 0, (-48), 16, true)) (RtSaved.MemFacts.StpPay pins mapping (352, 0, (-48), 16, true) (1#5) (2#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (352, 0, (-48), 16, true)) true 16)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 352 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (352, 0, (-48), 16, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_352).1) codeD) (RtSaved.MemFacts.StpPay pins mapping (352, 0, (-48), 16, true) (1#5) (2#5)) (fun _ _ _ g _ h => RtSaved.MemFacts.StpPay.transport g h) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (352, 0, (-48), 16, true)) true 16) nodup
    (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (2#7)) NativeEntryBodyMem.Stp.writes 617
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapValueMemFacts.memEV_Stp real spec config rows mapping dataStatic pinAligned (MemSteps.step_352).1 rfl (2#7) (1#5) (2#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_352).2.1 (MemSteps.step_352).2.2.2.1 (MemSteps.step_352).2.2.2.2 rfl rfl (MemSteps.step_352).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 352 pins table catalogue static 0xac 0xa9010be1
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 352 pins table catalogue static 0xac 0xa9010be1
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (2#7)) (by decide +kernel) x inv.core)

/-- step 353 @+0xb0 STP64_off a9020be1 (Stp {'Rt': 1, 'Rn': 31, 'Rt2': 2, 'imm7': 4}) -/
theorem step_353 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 353 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 353 + 1 ≤ capacity)
    (drawBound : drawsBefore 353 + 1 ≤ drawsBefore (353 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 353)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (353 + 1)) (MemNextE.MemRE spec mapping 353 (RtSaved.accPA pins mapping (353, 0, (-32), 16, true)) (RtSaved.MemFacts.StpPay pins mapping (353, 0, (-32), 16, true) (1#5) (2#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (353, 0, (-32), 16, true)) true 16)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 353 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (353, 0, (-32), 16, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_353).1) codeD) (RtSaved.MemFacts.StpPay pins mapping (353, 0, (-32), 16, true) (1#5) (2#5)) (fun _ _ _ g _ h => RtSaved.MemFacts.StpPay.transport g h) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (353, 0, (-32), 16, true)) true 16) nodup
    (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (4#7)) NativeEntryBodyMem.Stp.writes 617
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapValueMemFacts.memEV_Stp real spec config rows mapping dataStatic pinAligned (MemSteps.step_353).1 rfl (4#7) (1#5) (2#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_353).2.1 (MemSteps.step_353).2.2.2.1 (MemSteps.step_353).2.2.2.2 rfl rfl (MemSteps.step_353).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 353 pins table catalogue static 0xb0 0xa9020be1
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 353 pins table catalogue static 0xb0 0xa9020be1
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (4#7)) (by decide +kernel) x inv.core)

/-- step 354 @+0xb4 LDP64_off a9437bf3 (Ldp {'Rt': 19, 'Rn': 31, 'Rt2': 30, 'imm7': 6}) -/
theorem step_354 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 354 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 354 + 1 ≤ capacity)
    (drawBound : drawsBefore 354 + 1 ≤ drawsBefore (354 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 354)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (354 + 1)) (MemNextE.MemRE spec mapping 354 (fun _ => False) (RtSaved3.MemFacts2.LdpPay2 pins mapping (354, 0, (-16), 16, false) (19#5) (30#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (354, 0, (-16), 16, false)) false 16)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 354 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (RtSaved3.MemFacts2.LdpPay2 pins mapping (354, 0, (-16), 16, false) (19#5) (30#5)) (fun _ _ _ _ m h => RtSaved3.MemFacts2.LdpPay2.transport m h) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (354, 0, (-16), 16, false)) false 16) nodup
    (NativeEntryBodyDispatch.Ldp.selected (19#5) (30#5) (6#7)) NativeEntryBodyMem.Ldp.writes 611
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapValueMemFacts.memEV_Ldp real spec config rows mapping dataStatic pinAligned (MemSteps.step_354).1 rfl (6#7) (19#5) (30#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_354).2.1 (MemSteps.step_354).2.2.2.1 (MemSteps.step_354).2.2.2.2 rfl rfl (MemSteps.step_354).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 354 pins table catalogue static 0xb4 0xa9437bf3
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 354 pins table catalogue static 0xb4 0xa9437bf3
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldp.selected (19#5) (30#5) (6#7)) (by decide +kernel) x inv.core)

/-- step 355 @+0xb8 STP64_off a9030be1 (Stp {'Rt': 1, 'Rn': 31, 'Rt2': 2, 'imm7': 6}) -/
theorem step_355 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 355 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 355 + 1 ≤ capacity)
    (drawBound : drawsBefore 355 + 1 ≤ drawsBefore (355 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 355)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (355 + 1)) (MemNextE.MemRE spec mapping 355 (RtSaved.accPA pins mapping (355, 0, (-16), 16, true)) (RtSaved.MemFacts.StpPay pins mapping (355, 0, (-16), 16, true) (1#5) (2#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (355, 0, (-16), 16, true)) true 16)) :=
  ReleaseProfile.DefaultHeapEntryMem.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 355 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (355, 0, (-16), 16, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_355).1) codeD) (RtSaved.MemFacts.StpPay pins mapping (355, 0, (-16), 16, true) (1#5) (2#5)) (fun _ _ _ g _ h => RtSaved.MemFacts.StpPay.transport g h) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (355, 0, (-16), 16, true)) true 16) nodup
    (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (6#7)) NativeEntryBodyMem.Stp.writes 617
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapValueMemFacts.memEV_Stp real spec config rows mapping dataStatic pinAligned (MemSteps.step_355).1 rfl (6#7) (1#5) (2#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_355).2.1 (MemSteps.step_355).2.2.2.1 (MemSteps.step_355).2.2.2.2 rfl rfl (MemSteps.step_355).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 355 pins table catalogue static 0xb8 0xa9030be1
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 355 pins table catalogue static 0xb8 0xa9030be1
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (6#7)) (by decide +kernel) x inv.core)

end ReleaseProfile.DefaultHeapValueMemRows
