-- Generated current-profile branch routes from signed runtime14 rows.
import DefaultRuntimeStepEvidence
import DefaultRuntimeBranchTails
import DefaultRuntimeBranchRoute
import ReleaseR14.Next.Bcond_00
import ReleaseR14.Next.BranchB_00
import ReleaseR14.Next.Branch_00
import NativeR14Ret.Extend
import PipeR14.PinLink
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
attribute [local instance 10] Classical.propDecidable

#check "CURRENT_DECL step_c04_7"
theorem step_c04_7 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 7 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c04) (hpath : ArmCertPipe.PathOK (extend inputs D_c04) guards_c04)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 7 ≤ past (7 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 7 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 4) (by decide) rfl
    (c := (0x34, 0x54000162)) (by decide) offset_c04 budget 7 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 2#4 11#19 = BitVec.ofNat 32 (0x34, 0x54000162).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c04 σ0_c04 inputs.length plan_c04 = some (D_c04, σf) := by
    have hD := compiles_D_c04
    rw [← hlen] at hD
    cases hq : compileRun regions_c04 σ0_c04 inputs.length plan_c04 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c04 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 81) (z := 82) (c := 83) (v := 84) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c04) (.cond 0x2#4 81 82 83 84 false) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 2#4 x.regs false hg
  have hnext : (if Crypto.BcondCore.bcondC 2#4 x.regs then
      x.regs._PC + sign_extend (11#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c04 8 := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c04 budget 7 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 2#4 11#19) 69 (fun _ => base + offset_c04 8) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 2#4 11#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c04 7 + sign_extend (11#19 ++ 0#2) 64 = BitVec.ofNat 64 0x391870 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c04 _ _ mem
  have ok : (compileRun regions_c04 σ0_c04 inputs.length plan_c04).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 7) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c04_7

#check "CURRENT_DECL step_c04_15"
theorem step_c04_15 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 15 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c04) (hpath : ArmCertPipe.PathOK (extend inputs D_c04) guards_c04)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 15 ≤ past (15 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 15 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 4) (by decide) rfl
    (c := (0x6c, 0x540000eb)) (by decide) offset_c04 budget 15 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 7#19 = BitVec.ofNat 32 (0x6c, 0x540000eb).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c04 σ0_c04 inputs.length plan_c04 = some (D_c04, σf) := by
    have hD := compiles_D_c04
    rw [← hlen] at hD
    cases hq : compileRun regions_c04 σ0_c04 inputs.length plan_c04 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c04 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 90) (z := 91) (c := 92) (v := 93) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c04) (.cond 0xb#4 90 91 92 93 false) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 11#4 x.regs false hg
  have hnext : (if Crypto.BcondCore.bcondC 11#4 x.regs then
      x.regs._PC + sign_extend (7#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c04 16 := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c04 budget 15 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 7#19) 69 (fun _ => base + offset_c04 16) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 11#4 7#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c04 15 + sign_extend (7#19 ++ 0#2) 64 = BitVec.ofNat 64 0x391898 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c04 _ _ mem
  have ok : (compileRun regions_c04 σ0_c04 inputs.length plan_c04).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 15) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c04_15

#check "CURRENT_DECL step_c04_12"
theorem step_c04_12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 12 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c04)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 12 ≤ past (12 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 12 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 4) (by decide) rfl
    (c := (0x48, 0x14000007)) (by decide) offset_c04 budget 12 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.B.selected 7#26 = BitVec.ofNat 32 (0x48, 0x14000007).2 := by decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c04 budget 12 catalogue room page (by decide)
    (NativeEntryBodyDispatch.B.selected 7#26) 67 (fun _ => base + offset_c04 13) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichB.tail_at real x 7#26 (by rw [NativeEntryCallerRegisters.bl_target, inv.core.v1.pc, BitVec.add_assoc, show offset_c04 12 + sign_extend (7#26 ++ 0#2) 64 = BitVec.ofNat 64 0x391874 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) _ (by first | (simp only [NativeR14B.tbnzTarget, NativeR14B.cbz32Target, NativeEntryCallerParts.blTarget]; rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide) | (rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide)))
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c04 _ _ mem
  have ok : (compileRun regions_c04 σ0_c04 inputs.length plan_c04).isSome = true := by
    have hc := compiles_D_c04
    rw [← hlen] at hc
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 12) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c04_12

#check "CURRENT_DECL step_c04_3"
theorem step_c04_3 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 3 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c04) (hpath : ArmCertPipe.PathOK (extend inputs D_c04) guards_c04)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 3 ≤ past (3 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 3 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 4) (by decide) rfl
    (c := (0xc, 0x370000e1)) (by decide) offset_c04 budget 3 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Tbnz32.selected 1#5 7#14 = BitVec.ofNat 32 (0xc, 0x370000e1).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c04 σ0_c04 inputs.length plan_c04 = some (D_c04, σf) := by
    have hD := compiles_D_c04
    rw [← hlen] at hD
    cases hq : compileRun regions_c04 σ0_c04 inputs.length plan_c04 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c04 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨1, by decide⟩) (i := 42) inv.extra hall
    (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c04) (.bit 42 0 true) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  have hc : NativeR14B.tbnzBit 1#5 x = 1#1 := by
    rw [NativeR14B.tbnzBit_iff]; show (HeapV2StepCerts.RegBind.regVal x (.x ⟨1, by decide⟩)).getLsbD 0 = true; rw [hreg]; exact hg
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c04 budget 3 catalogue room page (by decide)
    (NativeEntryBodyDispatch.Tbnz32.selected 1#5 7#14) 1009 (fun _ => base + offset_c04 4) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichTbnzTaken.tail_at real x 1#5 7#14 (by decide) hc (by show (x.regs._PC + sign_extend (7#14 ++ 0#2) 64).toNat < 2 ^ 55; rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c04 3 + sign_extend (7#14 ++ 0#2) 64 = BitVec.ofNat 64 0x391838 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) _ (by first | (simp only [NativeR14B.tbnzTarget, NativeR14B.cbz32Target, NativeEntryCallerParts.blTarget]; rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide) | (rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide)))
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c04 _ _ mem
  have ok : (compileRun regions_c04 σ0_c04 inputs.length plan_c04).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 3) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c04_3

#check "CURRENT_DECL exit_c04"
theorem exit_c04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 21 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c04) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∀ x, ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past 21 x →
      ∃ fin, modelStep real x = .ok () fin ∧
        ArmCertPipe.Physical.AgreesAt bytePA regions_c04 σ0_c04 inputs plan_c04 22 fin ∧
        fin.regs._PC = inputs.getD 71 0 ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
        ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping [] x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 4) (by decide) rfl
    (c := (0x84, 0xd65f03c0)) (by decide) offset_c04 budget 21 (by decide) x inv.core
  have hw : ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5 = BitVec.ofNat 32 (0x84, 0xd65f03c0).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c04 σ0_c04 inputs.length plan_c04 = some (D_c04, σf) := by
    have hD := compiles_D_c04
    rw [← hlen] at hD
    cases hq : compileRun regions_c04 σ0_c04 inputs.length plan_c04 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c04 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨30, by decide⟩) (i := 99) inv.extra hall
    (by rw [hlen]; decide)
  have hslot : (extend inputs D_c04).getD 99 0 = inputs.getD 71 0 := by
    have h := NativeR14Ret.extend_getD_def inputs D_c04 22 (by decide)
    rw [show inputs.length + 22 = 99 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c04[22]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 71)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c04.take 22)).getD 71 0 = inputs.getD 71 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have hlow : (x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val]).toNat < 2 ^ 55 := by
    have e : HeapV2StepCerts.RegBind.regVal x (.x ⟨30, by decide⟩) =
        x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] := rfl
    rw [← e, hreg, hslot]; omega
  have retPC : x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = inputs.getD 71 0 :=
    hreg.trans hslot
  obtain ⟨fin, run, pc, vh, mem, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.branchEventExit real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c04 budget 21 catalogue room page (by decide)
    (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) 94 (fun _ => inputs.getD 71 0) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) hlow _ retPC)
    nodup (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c04 _ _ mem
  have ok : (compileRun regions_c04 σ0_c04 inputs.length plan_c04).isSome = true := by rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 21) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, next, pc, z, dit, ev, choice⟩

#print axioms exit_c04

end ReleaseProfile.DefaultRuntime
