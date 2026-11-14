-- Runtime14 c00 concrete continuing steps, preserving physical bytes and events.
import DefaultRuntimeStepEvidence
import DefaultScalarEventRoute
import DefaultRuntimeScalarChoice
import PipeR14Mem.Physical.Steps_c00
import ReleaseR14.Pipe.StepClass

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView ArmBridge.Boundary
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000
namespace ReleaseProfile.DefaultRuntime
open PipeR14 PipeR14.Physical

#check "CURRENT_DECL step_c00_2"
theorem step_c00_2 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 2 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c00)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 2 ≤ past (2 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 2 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 0) (by decide) rfl
    (c := (0x8, 0x910003fd)) (by decide) offset_c00 budget 2 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.AddSp.selected 29#5 0#12 = BitVec.ofNat 32 (0x8, 0x910003fd).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c00 3 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c00 2 + 4#64 = offset_c00 3 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c00 budget 2 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.AddSp.tailX real x 29#5 0#12 (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_AddSp
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c00 _ _ hm

  obtain ⟨σf', hc⟩ := PipeR14.Physical.full_c00 inputs hlen
  have ok : (compileRun regions_c00 σ0_c00 inputs.length plan_c00).isSome = true := by rw [hc]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 2) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c00_2

#check "CURRENT_DECL step_c00_5"
theorem step_c00_5 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 5 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c00)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 5 ≤ past (5 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 5 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 0) (by decide) rfl
    (c := (0x14, 0x7100091f)) (by decide) offset_c00 budget 5 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubsImm32.selected 8#5 2#12 = BitVec.ofNat 32 (0x14, 0x7100091f).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c00 6 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c00 5 + 4#64 = offset_c00 6 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c00 budget 5 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubsImm32.tailX real x 8#5 2#12 2#64 (by decide) (by decide) (by decide))
    (by
      apply DefaultRuntimeScalarChoice.tail_SubsImm32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c00 _ _ hm

  obtain ⟨σf', hc⟩ := PipeR14.Physical.full_c00 inputs hlen
  have ok : (compileRun regions_c00 σ0_c00 inputs.length plan_c00).isSome = true := by rw [hc]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 5) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c00_5

#check "CURRENT_DECL step_c00_7"
theorem step_c00_7 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 7 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c00)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 7 ≤ past (7 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 7 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 0) (by decide) rfl
    (c := (0x1c, 0x51000508)) (by decide) offset_c00 budget 7 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubImm32.selected 8#5 8#5 1#12 = BitVec.ofNat 32 (0x1c, 0x51000508).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c00 8 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c00 7 + 4#64 = offset_c00 8 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c00 budget 7 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubImm32.tailX real x 8#5 8#5 1#12 1#64 (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_SubImm32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c00 _ _ hm

  obtain ⟨σf', hc⟩ := PipeR14.Physical.full_c00 inputs hlen
  have ok : (compileRun regions_c00 σ0_c00 inputs.length plan_c00).isSome = true := by rw [hc]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 7) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c00_7

#check "CURRENT_DECL step_c00_10"
theorem step_c00_10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 10 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c00)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 10 ≤ past (10 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 10 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 0) (by decide) rfl
    (c := (0x28, 0x8b130009)) (by decide) offset_c00 budget 10 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.AddShift64.selected 9#5 0#5 0#6 19#5 = BitVec.ofNat 32 (0x28, 0x8b130009).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c00 11 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c00 10 + 4#64 = offset_c00 11 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c00 budget 10 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.AddShift64.tailX real x 9#5 0#5 0#6 19#5 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_AddShift64
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c00 _ _ hm

  obtain ⟨σf', hc⟩ := PipeR14.Physical.full_c00 inputs hlen
  have ok : (compileRun regions_c00 σ0_c00 inputs.length plan_c00).isSome = true := by rw [hc]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 10) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c00_10

#check "CURRENT_DECL step_c00_12"
theorem step_c00_12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 12 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c00)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 12 ≤ past (12 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 12 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 0) (by decide) rfl
    (c := (0x30, 0x7100091f)) (by decide) offset_c00 budget 12 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubsImm32.selected 8#5 2#12 = BitVec.ofNat 32 (0x30, 0x7100091f).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c00 13 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c00 12 + 4#64 = offset_c00 13 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c00 budget 12 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubsImm32.tailX real x 8#5 2#12 2#64 (by decide) (by decide) (by decide))
    (by
      apply DefaultRuntimeScalarChoice.tail_SubsImm32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c00 _ _ hm

  obtain ⟨σf', hc⟩ := PipeR14.Physical.full_c00 inputs hlen
  have ok : (compileRun regions_c00 σ0_c00 inputs.length plan_c00).isSome = true := by rw [hc]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 12) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c00_12

#check "CURRENT_DECL step_c00_14"
theorem step_c00_14 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 14 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c00)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 14 ≤ past (14 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 14 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 0) (by decide) rfl
    (c := (0x38, 0x51000508)) (by decide) offset_c00 budget 14 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubImm32.selected 8#5 8#5 1#12 = BitVec.ofNat 32 (0x38, 0x51000508).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c00 15 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c00 14 + 4#64 = offset_c00 15 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c00 budget 14 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubImm32.tailX real x 8#5 8#5 1#12 1#64 (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_SubImm32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c00 _ _ hm

  obtain ⟨σf', hc⟩ := PipeR14.Physical.full_c00 inputs hlen
  have ok : (compileRun regions_c00 σ0_c00 inputs.length plan_c00).isSome = true := by rw [hc]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 14) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c00_14

#check "CURRENT_DECL step_c00_16"
theorem step_c00_16 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 16 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c00)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 16 ≤ past (16 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 16 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 0) (by decide) rfl
    (c := (0x40, 0x52800028)) (by decide) offset_c00 budget 16 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Movz32.selected 8#5 1#16 = BitVec.ofNat 32 (0x40, 0x52800028).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c00 17 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c00 16 + 4#64 = offset_c00 17 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c00 budget 16 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.Movz32.tailX real x 8#5 1#16 1#64 (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_Movz32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c00 _ _ hm

  obtain ⟨σf', hc⟩ := PipeR14.Physical.full_c00 inputs hlen
  have ok : (compileRun regions_c00 σ0_c00 inputs.length plan_c00).isSome = true := by rw [hc]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 16) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c00_16

#check "CURRENT_DECL step_c00_17"
theorem step_c00_17 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 17 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c00)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 17 ≤ past (17 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 17 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 0) (by decide) rfl
    (c := (0x44, 0xaa130500)) (by decide) offset_c00 budget 17 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.OrrShift64.selected 0#5 8#5 1#6 19#5 = BitVec.ofNat 32 (0x44, 0xaa130500).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c00 18 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c00 17 + 4#64 = offset_c00 18 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c00 budget 17 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.OrrShift64.tailX real x 0#5 8#5 1#6 19#5 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_OrrShift64
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c00 _ _ hm

  obtain ⟨σf', hc⟩ := PipeR14.Physical.full_c00 inputs hlen
  have ok : (compileRun regions_c00 σ0_c00 inputs.length plan_c00).isSome = true := by rw [hc]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 17) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c00_17

end ReleaseProfile.DefaultRuntime
