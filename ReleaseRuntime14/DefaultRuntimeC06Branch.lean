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

#check "CURRENT_DECL step_c06_8"
theorem step_c06_8 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 8 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c06) (hpath : ArmCertPipe.PathOK (extend inputs D_c06) guards_c06)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 8 ≤ past (8 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 8 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x20, 0x540001eb)) (by decide) offset_c06 budget 8 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 15#19 = BitVec.ofNat 32 (0x20, 0x540001eb).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c06 σ0_c06 inputs.length plan_c06 = some (D_c06, σf) := by
    have hD := compiles_D_c06
    rw [← hlen] at hD
    cases hq : compileRun regions_c06 σ0_c06 inputs.length plan_c06 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c06 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 110) (z := 111) (c := 112) (v := 113) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c06) (.cond 0xb#4 110 111 112 113 false) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 11#4 x.regs false hg
  have hnext : (if Crypto.BcondCore.bcondC 11#4 x.regs then
      x.regs._PC + sign_extend (15#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c06 9 := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 8 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 15#19) 69 (fun _ => base + offset_c06 9) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 11#4 15#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 8 + sign_extend (15#19 ++ 0#2) 64 = BitVec.ofNat 64 0x391bc8 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c06 _ _ mem
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 8) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c06_8

#check "CURRENT_DECL step_c06_13"
theorem step_c06_13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 13 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c06) (hpath : ArmCertPipe.PathOK (extend inputs D_c06) guards_c06)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 13 ≤ past (13 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 13 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x34, 0x54000060)) (by decide) offset_c06 budget 13 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 0#4 3#19 = BitVec.ofNat 32 (0x34, 0x54000060).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c06 σ0_c06 inputs.length plan_c06 = some (D_c06, σf) := by
    have hD := compiles_D_c06
    rw [← hlen] at hD
    cases hq : compileRun regions_c06 σ0_c06 inputs.length plan_c06 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c06 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 116) (z := 117) (c := 118) (v := 119) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c06) (.cond 0x0#4 116 117 118 119 true) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 0#4 x.regs true hg
  have hnext : (if Crypto.BcondCore.bcondC 0#4 x.regs then
      x.regs._PC + sign_extend (3#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c06 14 := by
    rw [ite_eq_left (dec.mpr rfl), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 13 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 0#4 3#19) 69 (fun _ => base + offset_c06 14) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 0#4 3#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 13 + sign_extend (3#19 ++ 0#2) 64 = BitVec.ofNat 64 0x391bac by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c06 _ _ mem
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 13) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c06_13

#check "CURRENT_DECL exit_c06"
theorem exit_c06 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 20 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c06) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∀ x, ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past 20 x →
      ∃ fin, modelStep real x = .ok () fin ∧
        ArmCertPipe.Physical.AgreesAt bytePA regions_c06 σ0_c06 inputs plan_c06 21 fin ∧
        fin.regs._PC = inputs.getD 99 0 ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
        ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping [] x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x58, 0xd65f03c0)) (by decide) offset_c06 budget 20 (by decide) x inv.core
  have hw : ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5 = BitVec.ofNat 32 (0x58, 0xd65f03c0).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c06 σ0_c06 inputs.length plan_c06 = some (D_c06, σf) := by
    have hD := compiles_D_c06
    rw [← hlen] at hD
    cases hq : compileRun regions_c06 σ0_c06 inputs.length plan_c06 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c06 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨30, by decide⟩) (i := 127) inv.extra hall
    (by rw [hlen]; decide)
  have hslot : (extend inputs D_c06).getD 127 0 = inputs.getD 99 0 := by
    have h := NativeR14Ret.extend_getD_def inputs D_c06 22 (by decide)
    rw [show inputs.length + 22 = 127 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c06[22]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 99)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c06.take 22)).getD 99 0 = inputs.getD 99 0 :=
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
    (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 20 catalogue room page (by decide)
    (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) 94 (fun _ => inputs.getD 99 0) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) hlow _ retPC)
    nodup (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c06 _ _ mem
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 20) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, next, pc, z, dit, ev, choice⟩

#print axioms exit_c06

end ReleaseProfile.DefaultRuntime
