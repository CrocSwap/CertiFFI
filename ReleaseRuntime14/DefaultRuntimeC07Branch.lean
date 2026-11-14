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

#check "CURRENT_DECL step_c07_8"
theorem step_c07_8 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 8 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c07) (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 8 ≤ past (8 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 8 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x20, 0x540001eb)) (by decide) offset_c07 budget 8 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 15#19 = BitVec.ofNat 32 (0x20, 0x540001eb).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c07 σ0_c07 inputs.length plan_c07 = some (D_c07, σf) := by
    have hD := compiles_D_c07
    rw [← hlen] at hD
    cases hq : compileRun regions_c07 σ0_c07 inputs.length plan_c07 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c07 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 110) (z := 111) (c := 112) (v := 113) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c07) (.cond 0xb#4 110 111 112 113 true) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 11#4 x.regs true hg
  have hnext : (if Crypto.BcondCore.bcondC 11#4 x.regs then
      x.regs._PC + sign_extend (15#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c07 9 := by
    rw [ite_eq_left (dec.mpr rfl), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 8 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 15#19) 69 (fun _ => base + offset_c07 9) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 11#4 15#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 8 + sign_extend (15#19 ++ 0#2) 64 = BitVec.ofNat 64 0x391bc8 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ mem
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 8) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_8

#check "CURRENT_DECL step_c07_12"
theorem step_c07_12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 12 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c07) (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 12 ≤ past (12 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 12 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x34, 0x54000060)) (by decide) offset_c07 budget 12 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 0#4 3#19 = BitVec.ofNat 32 (0x34, 0x54000060).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c07 σ0_c07 inputs.length plan_c07 = some (D_c07, σf) := by
    have hD := compiles_D_c07
    rw [← hlen] at hD
    cases hq : compileRun regions_c07 σ0_c07 inputs.length plan_c07 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c07 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 115) (z := 116) (c := 117) (v := 118) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c07) (.cond 0x0#4 115 116 117 118 true) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 0#4 x.regs true hg
  have hnext : (if Crypto.BcondCore.bcondC 0#4 x.regs then
      x.regs._PC + sign_extend (3#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c07 13 := by
    rw [ite_eq_left (dec.mpr rfl), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 12 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 0#4 3#19) 69 (fun _ => base + offset_c07 13) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 0#4 3#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 12 + sign_extend (3#19 ++ 0#2) 64 = BitVec.ofNat 64 0x391bac by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ mem
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 12) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_12

#check "CURRENT_DECL step_c07_9"
theorem step_c07_9 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 9 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c07) (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 9 ≤ past (9 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 9 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x5c, 0x34fffe88)) (by decide) offset_c07 budget 9 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Cbz32.selected 8#5 524276#19 = BitVec.ofNat 32 (0x5c, 0x34fffe88).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c07 σ0_c07 inputs.length plan_c07 = some (D_c07, σf) := by
    have hD := compiles_D_c07
    rw [← hlen] at hD
    cases hq : compileRun regions_c07 σ0_c07 inputs.length plan_c07 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c07 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨8, by decide⟩) (i := 107) inv.extra hall
    (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c07) (.zero 107 true true) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  have hc : NativeR14B.cbz32Cond 8#5 x := by
    rw [NativeR14B.cbz32Cond_iff]; show (HeapV2StepCerts.RegBind.regVal x (.x ⟨8, by decide⟩)).setWidth 32 = 0#32; rw [hreg]; exact of_decide_eq_true hg
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 9 catalogue room page (by decide)
    (NativeEntryBodyDispatch.Cbz32.selected 8#5 524276#19) 118 (fun _ => base + offset_c07 10) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichCbzTaken.tail_at real x 8#5 524276#19 (by decide) hc (by show (x.regs._PC + sign_extend (524276#19 ++ 0#2) 64).toNat < 2 ^ 55; rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c07 9 + sign_extend (524276#19 ++ 0#2) 64 = BitVec.ofNat 64 0x391b98 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) _ (by first | (simp only [NativeR14B.tbnzTarget, NativeR14B.cbz32Target, NativeEntryCallerParts.blTarget]; rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide) | (rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide)))
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ mem
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 9) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c07_9

#check "CURRENT_DECL exit_c07"
theorem exit_c07 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 19 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c07) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∀ x, ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past 19 x →
      ∃ fin, modelStep real x = .ok () fin ∧
        ArmCertPipe.Physical.AgreesAt bytePA regions_c07 σ0_c07 inputs plan_c07 20 fin ∧
        fin.regs._PC = inputs.getD 99 0 ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
        ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping [] x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 7) (by decide) rfl
    (c := (0x58, 0xd65f03c0)) (by decide) offset_c07 budget 19 (by decide) x inv.core
  have hw : ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5 = BitVec.ofNat 32 (0x58, 0xd65f03c0).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c07 σ0_c07 inputs.length plan_c07 = some (D_c07, σf) := by
    have hD := compiles_D_c07
    rw [← hlen] at hD
    cases hq : compileRun regions_c07 σ0_c07 inputs.length plan_c07 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c07 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨30, by decide⟩) (i := 126) inv.extra hall
    (by rw [hlen]; decide)
  have hslot : (extend inputs D_c07).getD 126 0 = inputs.getD 99 0 := by
    have h := NativeR14Ret.extend_getD_def inputs D_c07 21 (by decide)
    rw [show inputs.length + 21 = 126 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c07[21]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 99)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c07.take 21)).getD 99 0 = inputs.getD 99 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have hlow : (x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val]).toNat < 2 ^ 55 := by
    have e : HeapV2StepCerts.RegBind.regVal x (.x ⟨30, by decide⟩) =
        x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] := rfl
    rw [← e, hreg, hslot]; omega
  have retPC : x.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = inputs.getD 99 0 :=
    hreg.trans hslot
  obtain ⟨fin, run, pc, vh, mem, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.branchEventExit real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget 19 catalogue room page (by decide)
    (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) 94 (fun _ => inputs.getD 99 0) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) hlow _ retPC)
    nodup (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c07 _ _ mem
  have ok : (compileRun regions_c07 σ0_c07 inputs.length plan_c07).isSome = true := by rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 19) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, next, pc, z, dit, ev, choice⟩

#print axioms exit_c07

end ReleaseProfile.DefaultRuntime
