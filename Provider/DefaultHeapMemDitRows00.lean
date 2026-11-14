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

/-- step 11 @+0x2c STP64_off a9037bf3 (Stp {'Rt': 19, 'Rn': 31, 'Rt2': 30, 'imm7': 6}) -/
theorem step_11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 11 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 11 + 1 ≤ capacity)
    (drawBound : drawsBefore 11 + 1 ≤ drawsBefore (11 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 11)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (11 + 1)) (fun s f => (MemNextE.MemRE spec mapping 11 (RtSaved.accPA pins mapping (11, 0, (-16), 16, true)) (RtSaved.MemFacts.StpPay pins mapping (11, 0, (-16), 16, true) (19#5) (30#5)) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (11, 0, (-16), 16, true)) true 16)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 11 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (11, 0, (-16), 16, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_11).1) codeD) (RtSaved.MemFacts.StpPay pins mapping (11, 0, (-16), 16, true) (19#5) (30#5)) (fun _ _ _ g _ h => RtSaved.MemFacts.StpPay.transport g h) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (11, 0, (-16), 16, true)) true 16) nodup
    (NativeEntryBodyDispatch.Stp.selected (19#5) (30#5) (6#7)) NativeEntryBodyMem.Stp.writes 617
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapSavedMemFacts.memEP_Stp real spec config rows mapping dataStatic pinAligned (MemSteps.step_11).1 rfl (6#7) (19#5) (30#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_11).2.1 (MemSteps.step_11).2.2.2.1 (MemSteps.step_11).2.2.2.2 rfl rfl (MemSteps.step_11).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 11 pins table catalogue static 0x2c 0xa9037bf3
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 11 pins table catalogue static 0x2c 0xa9037bf3
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (19#5) (30#5) (6#7)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_11

/-- step 18 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_18 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 18 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 18 + 1 ≤ capacity)
    (drawBound : drawsBefore 18 + 1 ≤ drawsBefore (18 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 18)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (18 + 1)) (fun s f => (MemNextE.MemRE spec mapping 18 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (18, 2, 0, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 18 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (18, 2, 0, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_18).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_18).2.1 (MemSteps.step_18).2.2.2 rfl rfl (MemSteps.step_18).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 18 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 18 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_18

/-- step 19 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_19 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 19 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 19 + 1 ≤ capacity)
    (drawBound : drawsBefore 19 + 1 ≤ drawsBefore (19 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 19)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (19 + 1)) (fun s f => (MemNextE.MemRE spec mapping 19 (RtSaved.accPA pins mapping (19, 0, (-64), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (19, 0, (-64), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 19 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (19, 0, (-64), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_19).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (19, 0, (-64), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_19).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_19).2.1 (MemSteps.step_19).2.2.2 rfl rfl (MemSteps.step_19).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 19 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 19 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_19

/-- step 22 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_22 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 22 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 22 + 1 ≤ capacity)
    (drawBound : drawsBefore 22 + 1 ≤ drawsBefore (22 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 22)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (22 + 1)) (fun s f => (MemNextE.MemRE spec mapping 22 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (22, 2, 1, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 22 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (22, 2, 1, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_22).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_22).2.1 (MemSteps.step_22).2.2.2 rfl rfl (MemSteps.step_22).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 22 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 22 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_22

/-- step 23 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_23 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 23 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 23 + 1 ≤ capacity)
    (drawBound : drawsBefore 23 + 1 ≤ drawsBefore (23 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 23)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (23 + 1)) (fun s f => (MemNextE.MemRE spec mapping 23 (RtSaved.accPA pins mapping (23, 0, (-63), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (23, 0, (-63), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 23 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (23, 0, (-63), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_23).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (23, 0, (-63), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_23).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_23).2.1 (MemSteps.step_23).2.2.2 rfl rfl (MemSteps.step_23).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 23 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 23 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_23

/-- step 26 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_26 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 26 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 26 + 1 ≤ capacity)
    (drawBound : drawsBefore 26 + 1 ≤ drawsBefore (26 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 26)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (26 + 1)) (fun s f => (MemNextE.MemRE spec mapping 26 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (26, 2, 2, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 26 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (26, 2, 2, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_26).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_26).2.1 (MemSteps.step_26).2.2.2 rfl rfl (MemSteps.step_26).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 26 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 26 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_26

/-- step 27 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_27 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 27 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 27 + 1 ≤ capacity)
    (drawBound : drawsBefore 27 + 1 ≤ drawsBefore (27 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 27)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (27 + 1)) (fun s f => (MemNextE.MemRE spec mapping 27 (RtSaved.accPA pins mapping (27, 0, (-62), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (27, 0, (-62), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 27 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (27, 0, (-62), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_27).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (27, 0, (-62), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_27).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_27).2.1 (MemSteps.step_27).2.2.2 rfl rfl (MemSteps.step_27).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 27 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 27 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_27

/-- step 30 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_30 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 30 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 30 + 1 ≤ capacity)
    (drawBound : drawsBefore 30 + 1 ≤ drawsBefore (30 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 30)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (30 + 1)) (fun s f => (MemNextE.MemRE spec mapping 30 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (30, 2, 3, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 30 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (30, 2, 3, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_30).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_30).2.1 (MemSteps.step_30).2.2.2 rfl rfl (MemSteps.step_30).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 30 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 30 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_30

/-- step 31 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_31 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 31 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 31 + 1 ≤ capacity)
    (drawBound : drawsBefore 31 + 1 ≤ drawsBefore (31 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 31)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (31 + 1)) (fun s f => (MemNextE.MemRE spec mapping 31 (RtSaved.accPA pins mapping (31, 0, (-61), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (31, 0, (-61), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 31 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (31, 0, (-61), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_31).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (31, 0, (-61), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_31).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_31).2.1 (MemSteps.step_31).2.2.2 rfl rfl (MemSteps.step_31).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 31 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 31 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_31

/-- step 34 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_34 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 34 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 34 + 1 ≤ capacity)
    (drawBound : drawsBefore 34 + 1 ≤ drawsBefore (34 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 34)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (34 + 1)) (fun s f => (MemNextE.MemRE spec mapping 34 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (34, 2, 4, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 34 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (34, 2, 4, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_34).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_34).2.1 (MemSteps.step_34).2.2.2 rfl rfl (MemSteps.step_34).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 34 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 34 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_34

/-- step 35 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_35 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 35 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 35 + 1 ≤ capacity)
    (drawBound : drawsBefore 35 + 1 ≤ drawsBefore (35 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 35)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (35 + 1)) (fun s f => (MemNextE.MemRE spec mapping 35 (RtSaved.accPA pins mapping (35, 0, (-60), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (35, 0, (-60), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 35 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (35, 0, (-60), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_35).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (35, 0, (-60), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_35).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_35).2.1 (MemSteps.step_35).2.2.2 rfl rfl (MemSteps.step_35).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 35 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 35 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_35

/-- step 38 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_38 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 38 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 38 + 1 ≤ capacity)
    (drawBound : drawsBefore 38 + 1 ≤ drawsBefore (38 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 38)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (38 + 1)) (fun s f => (MemNextE.MemRE spec mapping 38 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (38, 2, 5, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 38 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (38, 2, 5, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_38).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_38).2.1 (MemSteps.step_38).2.2.2 rfl rfl (MemSteps.step_38).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 38 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 38 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_38

/-- step 39 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_39 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 39 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 39 + 1 ≤ capacity)
    (drawBound : drawsBefore 39 + 1 ≤ drawsBefore (39 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 39)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (39 + 1)) (fun s f => (MemNextE.MemRE spec mapping 39 (RtSaved.accPA pins mapping (39, 0, (-59), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (39, 0, (-59), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 39 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (39, 0, (-59), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_39).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (39, 0, (-59), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_39).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_39).2.1 (MemSteps.step_39).2.2.2 rfl rfl (MemSteps.step_39).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 39 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 39 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_39

/-- step 42 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_42 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 42 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 42 + 1 ≤ capacity)
    (drawBound : drawsBefore 42 + 1 ≤ drawsBefore (42 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 42)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (42 + 1)) (fun s f => (MemNextE.MemRE spec mapping 42 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (42, 2, 6, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 42 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (42, 2, 6, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_42).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_42).2.1 (MemSteps.step_42).2.2.2 rfl rfl (MemSteps.step_42).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 42 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 42 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_42

/-- step 43 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_43 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 43 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 43 + 1 ≤ capacity)
    (drawBound : drawsBefore 43 + 1 ≤ drawsBefore (43 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 43)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (43 + 1)) (fun s f => (MemNextE.MemRE spec mapping 43 (RtSaved.accPA pins mapping (43, 0, (-58), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (43, 0, (-58), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 43 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (43, 0, (-58), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_43).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (43, 0, (-58), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_43).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_43).2.1 (MemSteps.step_43).2.2.2 rfl rfl (MemSteps.step_43).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 43 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 43 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_43

/-- step 46 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_46 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 46 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 46 + 1 ≤ capacity)
    (drawBound : drawsBefore 46 + 1 ≤ drawsBefore (46 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 46)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (46 + 1)) (fun s f => (MemNextE.MemRE spec mapping 46 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (46, 2, 7, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 46 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (46, 2, 7, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_46).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_46).2.1 (MemSteps.step_46).2.2.2 rfl rfl (MemSteps.step_46).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 46 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 46 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_46

/-- step 47 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_47 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 47 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 47 + 1 ≤ capacity)
    (drawBound : drawsBefore 47 + 1 ≤ drawsBefore (47 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 47)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (47 + 1)) (fun s f => (MemNextE.MemRE spec mapping 47 (RtSaved.accPA pins mapping (47, 0, (-57), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (47, 0, (-57), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 47 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (47, 0, (-57), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_47).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (47, 0, (-57), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_47).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_47).2.1 (MemSteps.step_47).2.2.2 rfl rfl (MemSteps.step_47).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 47 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 47 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_47

/-- step 50 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_50 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 50 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 50 + 1 ≤ capacity)
    (drawBound : drawsBefore 50 + 1 ≤ drawsBefore (50 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 50)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (50 + 1)) (fun s f => (MemNextE.MemRE spec mapping 50 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (50, 2, 8, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 50 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (50, 2, 8, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_50).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_50).2.1 (MemSteps.step_50).2.2.2 rfl rfl (MemSteps.step_50).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 50 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 50 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_50

/-- step 51 @+0x134 STRB_post 38001464 (Strb {'Rt': 4, 'Rn': 3, 'imm9': 1}) -/
theorem step_51 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 51 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 51 + 1 ≤ capacity)
    (drawBound : drawsBefore 51 + 1 ≤ drawsBefore (51 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 51)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (51 + 1)) (fun s f => (MemNextE.MemRE spec mapping 51 (RtSaved.accPA pins mapping (51, 0, (-56), 1, true)) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (51, 0, (-56), 1, true)) true 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 51 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (RtSaved.accPA pins mapping (51, 0, (-56), 1, true)) (MemNext.codeD_mono (MemNext.accPA_sub (MemSteps.step_51).1) codeD) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (51, 0, (-56), 1, true)) true 1) nodup
    (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) NativeEntryBodyMem.Strb.writes 649
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Strb real spec config rows mapping dataStatic (MemSteps.step_51).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_51).2.1 (MemSteps.step_51).2.2.2 rfl rfl (MemSteps.step_51).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 51 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 51 pins table catalogue static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_51

/-- step 54 @+0x130 LDRB_post 38401424 (Ldrb {'Rt': 4, 'Rn': 1, 'imm9': 1}) -/
theorem step_54 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : ArmBridge.Draft.NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (room : 54 < budget) (page : base.toNat % 4096 = 0)
    (statusBound : drawsBefore 54 + 1 ≤ capacity)
    (drawBound : drawsBefore 54 + 1 ≤ drawsBefore (54 + 1)) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore 54)
      (ReleaseProfile.DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore (54 + 1)) (fun s f => (MemNextE.MemRE spec mapping 54 (fun _ => False) (fun _ _ => True) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (54, 2, 9, 1, false)) false 1)) s f ∧ f.regs.PSTATE.DIT = s.regs.PSTATE.DIT) :=
  ReleaseProfile.DefaultHeapMemoryDit.heap_mem_step real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 54 catalogue entry capacity drawsBefore 1 statusBound drawBound room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (fun _ _ => True) (fun _ _ _ _ _ _ => trivial) (by decide +kernel) (DataRecs.dataRecs spec (HeapV2E17.dataVA pins (54, 2, 9, 1, false)) false 1) nodup
    (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) NativeEntryBodyMem.Ldrb.writes 631
    (fun x => x.regs._PC + 4#64)
    (fun x _ => ReleaseProfile.DefaultHeapMemFacts.memE_Ldrb real spec config rows mapping dataStatic (MemSteps.step_54).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_54).2.1 (MemSteps.step_54).2.2.2 rfl rfl (MemSteps.step_54).2.2.1 catalogue x)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memNextPlaced spec config rows mapping base budget 54 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.core)
    (fun x inv => ReleaseProfile.DefaultHeapCode.memFetch spec config rows mapping base budget 54 pins table catalogue static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.core) (by decide)
#print axioms step_54

end ReleaseProfile.DefaultHeapMemDitRows
