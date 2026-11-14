-- Generated current physical steps from signed c07 class rows.
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

#check "CURRENT_DECL step_c07_3"
theorem step_c07_3 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 3 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 3 ≤ past (3 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 3 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0xc, 0x910003fd)) (by decide) offset_c07 budget 3 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.AddSp.selected 29#5 0#12 = BitVec.ofNat 32 (0xc, 0x910003fd).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c07 4 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 3 + 4#64 = offset_c07 4 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 3 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.AddSp.tailX real x 29#5 0#12 (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_AddSp
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ hm

  have hc : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).map Prod.fst = some D_c07 := by
    rw [hlen]
    exact compiles_D_c07
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 3) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_3

#check "CURRENT_DECL step_c07_6"
theorem step_c07_6 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 6 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 6 ≤ past (6 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 6 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x18, 0xaa0203f3)) (by decide) offset_c07 budget 6 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.OrrMov64.selected 19#5 0#6 2#5 = BitVec.ofNat 32 (0x18, 0xaa0203f3).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c07 7 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 6 + 4#64 = offset_c07 7 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 6 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.OrrMov64.tailX real x 19#5 0#6 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_OrrMov64
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ hm

  have hc : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).map Prod.fst = some D_c07 := by
    rw [hlen]
    exact compiles_D_c07
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 6) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_6

#check "CURRENT_DECL step_c07_7"
theorem step_c07_7 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 7 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 7 ≤ past (7 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 7 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x1c, 0x7100091f)) (by decide) offset_c07 budget 7 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubsImm32.selected 8#5 2#12 = BitVec.ofNat 32 (0x1c, 0x7100091f).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c07 8 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 7 + 4#64 = offset_c07 8 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 7 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubsImm32.tailX real x 8#5 2#12 2#64 (by decide) (by decide) (by decide))
    (by
      apply DefaultRuntimeScalarChoice.tail_SubsImm32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ hm

  have hc : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).map Prod.fst = some D_c07 := by
    rw [hlen]
    exact compiles_D_c07
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 7) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_7

#check "CURRENT_DECL step_c07_11"
theorem step_c07_11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 11 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 11 ≤ past (11 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 11 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x30, 0x7100051f)) (by decide) offset_c07 budget 11 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubsImm32.selected 8#5 1#12 = BitVec.ofNat 32 (0x30, 0x7100051f).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c07 12 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 11 + 4#64 = offset_c07 12 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 11 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubsImm32.tailX real x 8#5 1#12 1#64 (by decide) (by decide) (by decide))
    (by
      apply DefaultRuntimeScalarChoice.tail_SubsImm32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ hm

  have hc : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).map Prod.fst = some D_c07 := by
    rw [hlen]
    exact compiles_D_c07
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 11) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_11

#check "CURRENT_DECL step_c07_13"
theorem step_c07_13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 13 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 13 ≤ past (13 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 13 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x40, 0xd341fe68)) (by decide) offset_c07 budget 13 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.UbfmLsr1.selected 8#5 19#5 = BitVec.ofNat 32 (0x40, 0xd341fe68).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c07 14 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 13 + 4#64 = offset_c07 14 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 13 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.UbfmLsr1.tailX real x 8#5 19#5 (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_UbfmLsr1
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ hm

  have hc : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).map Prod.fst = some D_c07 := by
    rw [hlen]
    exact compiles_D_c07
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 13) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_13

#check "CURRENT_DECL step_c07_14"
theorem step_c07_14 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 14 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 14 ≤ past (14 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 14 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x44, 0x8b140009)) (by decide) offset_c07 budget 14 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.AddShift64.selected 9#5 0#5 0#6 20#5 = BitVec.ofNat 32 (0x44, 0x8b140009).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c07 15 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 14 + 4#64 = offset_c07 15 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 14 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.AddShift64.tailX real x 9#5 0#5 0#6 20#5 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨⟩)
    (by
      apply DefaultRuntimeScalarChoice.tail_AddShift64
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ hm

  have hc : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).map Prod.fst = some D_c07 := by
    rw [hlen]
    exact compiles_D_c07
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 14) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_14

end ReleaseProfile.DefaultRuntime
