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

#check "CURRENT_DECL step_c02_6"
theorem step_c02_6 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 6 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c02) (hpath : ArmCertPipe.PathOK (extend inputs D_c02) guards_c02)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 6 ≤ past (6 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c02 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 6 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 2) (by decide) rfl
    (c := (0x18, 0x540001eb)) (by decide) offset_c02 budget 6 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 15#19 = BitVec.ofNat 32 (0x18, 0x540001eb).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c02 σ0_c02 inputs.length plan_c02 = some (D_c02, σf) := by
    have hD := compiles_D_c02
    rw [← hlen] at hD
    cases hq : compileRun regions_c02 σ0_c02 inputs.length plan_c02 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c02 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 93) (z := 94) (c := 95) (v := 96) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c02) (.cond 0xb#4 93 94 95 96 false) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 11#4 x.regs false hg
  have hnext : (if Crypto.BcondCore.bcondC 11#4 x.regs then
      x.regs._PC + sign_extend (15#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c02 7 := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c02 budget 6 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 15#19) 69 (fun _ => base + offset_c02 7) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 11#4 15#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c02 6 + sign_extend (15#19 ++ 0#2) 64 = BitVec.ofNat 64 0x3917dc by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c02 _ _ mem
  have ok : (compileRun regions_c02 σ0_c02 inputs.length plan_c02).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 6) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c02_6

#check "CURRENT_DECL step_c02_13"
theorem step_c02_13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 13 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c02) (hpath : ArmCertPipe.PathOK (extend inputs D_c02) guards_c02)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 13 ≤ past (13 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c02 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 13 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 2) (by decide) rfl
    (c := (0x34, 0x540001cb)) (by decide) offset_c02 budget 13 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 14#19 = BitVec.ofNat 32 (0x34, 0x540001cb).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c02 σ0_c02 inputs.length plan_c02 = some (D_c02, σf) := by
    have hD := compiles_D_c02
    rw [← hlen] at hD
    cases hq : compileRun regions_c02 σ0_c02 inputs.length plan_c02 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c02 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 101) (z := 102) (c := 103) (v := 104) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c02) (.cond 0xb#4 101 102 103 104 true) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 11#4 x.regs true hg
  have hnext : (if Crypto.BcondCore.bcondC 11#4 x.regs then
      x.regs._PC + sign_extend (14#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c02 14 := by
    rw [ite_eq_left (dec.mpr rfl), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c02 budget 13 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 14#19) 69 (fun _ => base + offset_c02 14) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 11#4 14#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c02 13 + sign_extend (14#19 ++ 0#2) 64 = BitVec.ofNat 64 0x3917f4 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c02 _ _ mem
  have ok : (compileRun regions_c02 σ0_c02 inputs.length plan_c02).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 13) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c02_13

#check "CURRENT_DECL step_c02_14"
theorem step_c02_14 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 14 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c02) (hpath : ArmCertPipe.PathOK (extend inputs D_c02) guards_c02)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 14 ≤ past (14 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c02 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 14 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 2) (by decide) rfl
    (c := (0x6c, 0x34fffea8)) (by decide) offset_c02 budget 14 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Cbz32.selected 8#5 524277#19 = BitVec.ofNat 32 (0x6c, 0x34fffea8).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c02 σ0_c02 inputs.length plan_c02 = some (D_c02, σf) := by
    have hD := compiles_D_c02
    rw [← hlen] at hD
    cases hq : compileRun regions_c02 σ0_c02 inputs.length plan_c02 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c02 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨8, by decide⟩) (i := 98) inv.extra hall
    (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c02) (.zero 98 true true) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  have hc : NativeR14B.cbz32Cond 8#5 x := by
    rw [NativeR14B.cbz32Cond_iff]; show (HeapV2StepCerts.RegBind.regVal x (.x ⟨8, by decide⟩)).setWidth 32 = 0#32; rw [hreg]; exact of_decide_eq_true hg
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c02 budget 14 catalogue room page (by decide)
    (NativeEntryBodyDispatch.Cbz32.selected 8#5 524277#19) 118 (fun _ => base + offset_c02 15) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichCbzTaken.tail_at real x 8#5 524277#19 (by decide) hc (by show (x.regs._PC + sign_extend (524277#19 ++ 0#2) 64).toNat < 2 ^ 55; rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c02 14 + sign_extend (524277#19 ++ 0#2) 64 = BitVec.ofNat 64 0x3917c8 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) _ (by first | (simp only [NativeR14B.tbnzTarget, NativeR14B.cbz32Target, NativeEntryCallerParts.blTarget]; rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide) | (rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide)))
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c02 _ _ mem
  have ok : (compileRun regions_c02 σ0_c02 inputs.length plan_c02).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 14) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c02_14

#check "CURRENT_DECL exit_c02"
theorem exit_c02 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 19 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c02) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∀ x, ReleaseProfile.DefaultRuntime.Inv_c02 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past 19 x →
      ∃ fin, modelStep real x = .ok () fin ∧
        ArmCertPipe.Physical.AgreesAt bytePA regions_c02 σ0_c02 inputs plan_c02 20 fin ∧
        fin.regs._PC = inputs.getD 83 0 ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
        ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping [] x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 2) (by decide) rfl
    (c := (0x50, 0xd65f03c0)) (by decide) offset_c02 budget 19 (by decide) x inv.core
  have hw : ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5 = BitVec.ofNat 32 (0x50, 0xd65f03c0).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c02 σ0_c02 inputs.length plan_c02 = some (D_c02, σf) := by
    have hD := compiles_D_c02
    rw [← hlen] at hD
    cases hq : compileRun regions_c02 σ0_c02 inputs.length plan_c02 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c02 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨30, by decide⟩) (i := 111) inv.extra hall
    (by rw [hlen]; decide)
  have hslot : (extend inputs D_c02).getD 111 0 = inputs.getD 83 0 := by
    have h := NativeR14Ret.extend_getD_def inputs D_c02 22 (by decide)
    rw [show inputs.length + 22 = 111 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c02[22]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 83)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c02.take 22)).getD 83 0 = inputs.getD 83 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have hlow : (x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val]).toNat < 2 ^ 55 := by
    have e : HeapV2StepCerts.RegBind.regVal x (.x ⟨30, by decide⟩) =
        x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] := rfl
    rw [← e, hreg, hslot]; omega
  have retPC : x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = inputs.getD 83 0 :=
    hreg.trans hslot
  obtain ⟨fin, run, pc, vh, mem, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.branchEventExit real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c02 budget 19 catalogue room page (by decide)
    (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) 94 (fun _ => inputs.getD 83 0) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) hlow _ retPC)
    nodup (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c02 _ _ mem
  have ok : (compileRun regions_c02 σ0_c02 inputs.length plan_c02).isSome = true := by rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 19) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, next, pc, z, dit, ev, choice⟩

#print axioms exit_c02

end ReleaseProfile.DefaultRuntime
