-- Generated current physical steps from signed c05 class rows.
import DefaultRuntimeStepEvidence
import DefaultScalarEventRoute
import DefaultRuntimeScalarChoice
import ReleaseR14.Pipe.StepClass
import PipeR14.PinLink
import PipeR14.PlanChecks

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

#check "CURRENT_DECL step_c05_2"
theorem step_c05_2 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 2 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 2 ≤ past (2 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 2 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x8, 0x910003fd)) (by decide) offset_c05 budget 2 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.AddSp.selected 29#5 0#12 = BitVec.ofNat 32 (0x8, 0x910003fd).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c05 3 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 2 + 4#64 = offset_c05 3 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 2 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.AddSp.tailX real x 29#5 0#12 (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_AddSp
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c05 _ _ hm

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 2) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c05_2

#check "CURRENT_DECL step_c05_4"
theorem step_c05_4 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 4 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 4 ≤ past (4 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 4 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x28, 0xd341fc28)) (by decide) offset_c05 budget 4 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.UbfmLsr1.selected 8#5 1#5 = BitVec.ofNat 32 (0x28, 0xd341fc28).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c05 5 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 4 + 4#64 = offset_c05 5 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 4 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.UbfmLsr1.tailX real x 8#5 1#5 (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_UbfmLsr1
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c05 _ _ hm

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 4) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c05_4

#check "CURRENT_DECL step_c05_6"
theorem step_c05_6 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 6 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 6 ≤ past (6 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 6 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x30, 0xeb09011f)) (by decide) offset_c05 budget 6 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubsShift64ZRd.selected 8#5 0#6 9#5 = BitVec.ofNat 32 (0x30, 0xeb09011f).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c05 7 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 6 + 4#64 = offset_c05 7 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 6 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubsShift64ZRd.tailX real x 8#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide))
    (by
      apply DefaultRuntimeScalarChoice.tail_SubsShift64ZRd
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c05 _ _ hm

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 6) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c05_6

#check "CURRENT_DECL step_c05_8"
theorem step_c05_8 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 8 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 8 ≤ past (8 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 8 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x38, 0x8b080008)) (by decide) offset_c05 budget 8 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.AddShift64.selected 8#5 0#5 0#6 8#5 = BitVec.ofNat 32 (0x38, 0x8b080008).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c05 9 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 8 + 4#64 = offset_c05 9 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 8 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.AddShift64.tailX real x 8#5 0#5 0#6 8#5 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_AddShift64
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c05 _ _ hm

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 8) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c05_8

#check "CURRENT_DECL step_c05_9"
theorem step_c05_9 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 9 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 9 ≤ past (9 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 9 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x3c, 0x52800029)) (by decide) offset_c05 budget 9 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Movz32.selected 9#5 1#16 = BitVec.ofNat 32 (0x3c, 0x52800029).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c05 10 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 9 + 4#64 = offset_c05 10 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 9 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.Movz32.tailX real x 9#5 1#16 1#64 (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_Movz32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c05 _ _ hm

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 9) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c05_9

#check "CURRENT_DECL step_c05_11"
theorem step_c05_11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 11 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 11 ≤ past (11 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 11 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x44, 0xaa080533)) (by decide) offset_c05 budget 11 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.OrrShift64.selected 19#5 9#5 1#6 8#5 = BitVec.ofNat 32 (0x44, 0xaa080533).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c05 12 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 11 + 4#64 = offset_c05 12 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 11 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.OrrShift64.tailX real x 19#5 9#5 1#6 8#5 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_OrrShift64
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c05 _ _ hm

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 11) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c05_11

#check "CURRENT_DECL step_c05_14"
theorem step_c05_14 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 14 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 14 ≤ past (14 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 14 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x68, 0x7100091f)) (by decide) offset_c05 budget 14 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubsImm32.selected 8#5 2#12 = BitVec.ofNat 32 (0x68, 0x7100091f).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c05 15 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 14 + 4#64 = offset_c05 15 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 14 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubsImm32.tailX real x 8#5 2#12 2#64 (by decide) (by decide) (by decide))
    (by
      apply DefaultRuntimeScalarChoice.tail_SubsImm32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c05 _ _ hm

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 14) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c05_14

#check "CURRENT_DECL step_c05_17"
theorem step_c05_17 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 17 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 17 ≤ past (17 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 17 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x78, 0xaa1303e0)) (by decide) offset_c05 budget 17 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.OrrMov64.selected 0#5 0#6 19#5 = BitVec.ofNat 32 (0x78, 0xaa1303e0).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c05 18 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 17 + 4#64 = offset_c05 18 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 17 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.OrrMov64.tailX real x 0#5 0#6 19#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_OrrMov64
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c05 _ _ hm

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 17) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c05_17

end ReleaseProfile.DefaultRuntime
