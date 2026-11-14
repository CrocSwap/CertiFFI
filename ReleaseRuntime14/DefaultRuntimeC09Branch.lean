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

#check "CURRENT_DECL step_c09_3"
theorem step_c09_3 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 3 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c09) (hpath : ArmCertPipe.PathOK (extend inputs D_c09) guards_c09)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 3 ≤ past (3 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c09 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 3 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 9) (by decide) rfl
    (c := (0xc, 0x540000cb)) (by decide) offset_c09 budget 3 (by decide) x inv.core
  have hw : ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 6#19 = BitVec.ofNat 32 (0xc, 0x540000cb).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c09 σ0_c09 inputs.length plan_c09 = some (D_c09, σf) := by
    have hD := compiles_D_c09
    rw [← hlen] at hD
    cases hq : compileRun regions_c09 σ0_c09 inputs.length plan_c09 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c09 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hf := ArmCertPipe.Physical.flags_of_agreesAt (n := 41) (z := 42) (c := 43) (v := 44) inv.extra hall (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c09) (.cond 0xb#4 41 42 43 44 false) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  rw [← hf.1, ← hf.2.1, ← hf.2.2.1, ← hf.2.2.2] at hg
  have dec := PipeR14Next.cond_bridge 11#4 x.regs false hg
  have hnext : (if Crypto.BcondCore.bcondC 11#4 x.regs then
      x.regs._PC + sign_extend (6#19 ++ 0#2) 64 else x.regs._PC + 4#64) = base + offset_c09 4 := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c09 budget 3 catalogue room page (by decide)
    (ReleaseProfile.DefaultRuntimeBcondEventTail.W 11#4 6#19) 69 (fun _ => base + offset_c09 4) x inv.core
    (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x 11#4 6#19 (by decide) (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c09 3 + sign_extend (6#19 ++ 0#2) 64 = BitVec.ofNat 64 0x2baa84 by decide, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ hnext)
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c09 _ _ mem
  have ok : (compileRun regions_c09 σ0_c09 inputs.length plan_c09).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 3) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c09_3

#check "CURRENT_DECL step_c09_0"
theorem step_c09_0 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 0 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c09) (hpath : ArmCertPipe.PathOK (extend inputs D_c09) guards_c09)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (drawsNext : past 0 ≤ past (0 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c09 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 0 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 9) (by decide) rfl
    (c := (0x0, 0x370000c0)) (by decide) offset_c09 budget 0 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Tbnz32.selected 0#5 6#14 = BitVec.ofNat 32 (0x0, 0x370000c0).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c09 σ0_c09 inputs.length plan_c09 = some (D_c09, σf) := by
    have hD := compiles_D_c09
    rw [← hlen] at hD
    cases hq : compileRun regions_c09 σ0_c09 inputs.length plan_c09 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c09 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨0, by decide⟩) (i := 4) inv.extra hall
    (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c09) (.bit 4 0 false) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  have hc : ¬ NativeR14B.tbnzBit 0#5 x = 1#1 := by
    rw [NativeR14B.tbnzBit_iff]; show ¬ (HeapV2StepCerts.RegBind.regVal x (.x ⟨0, by decide⟩)).getLsbD 0 = true; rw [hreg, hg]; decide
  obtain ⟨fin, run, core, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c09 budget 0 catalogue room page (by decide)
    (NativeEntryBodyDispatch.Tbnz32.selected 0#5 6#14) 1009 (fun _ => base + offset_c09 1) x inv.core
    (ReleaseProfile.DefaultRuntimeBranch.RichTbnzNot.tail_at real x 0#5 6#14 (by decide) hc (by decide) _ (by first | (simp only [NativeR14B.tbnzTarget, NativeR14B.cbz32Target, NativeEntryCallerParts.blTarget]; rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide) | (rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1 <;> decide)))
    nodup rfl (hw ▸ ob)

  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c09 _ _ mem
  have ok : (compileRun regions_c09 σ0_c09 inputs.length plan_c09).isSome = true := by
    rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 0) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c09_0

end ReleaseProfile.DefaultRuntime
