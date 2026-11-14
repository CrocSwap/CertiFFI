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

#check "CURRENT_DECL exit_c11"
theorem exit_c11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 0 < budget)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54)
    (hlen : inputs.length = n0_c11) (hpath : ArmCertPipe.PathOK (extend inputs D_c11) guards_c11)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∀ x, ReleaseProfile.DefaultRuntime.Inv_c11 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past 0 x →
      ∃ fin, modelStep real x = .ok () fin ∧
        ArmCertPipe.Physical.AgreesAt bytePA regions_c11 σ0_c11 inputs plan_c11 1 fin ∧
        fin.regs._PC = base + BitVec.ofNat 64 0x2b6b2c ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
        ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping [] x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 11) (by decide) rfl
    (c := (0x0, 0x370000d3)) (by decide) offset_c11 budget 0 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Tbnz32.selected 19#5 6#14 = BitVec.ofNat 32 (0x0, 0x370000d3).2 := by decide
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c11 σ0_c11 inputs.length plan_c11 = some (D_c11, σf) := by
    have hD := compiles_D_c11
    rw [← hlen] at hD
    cases hq : compileRun regions_c11 σ0_c11 inputs.length plan_c11 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c11 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hreg := ArmCertPipe.Physical.regVal_of_agreesAt (r := .x ⟨19, by decide⟩) (i := 19) inv.extra hall
    (by rw [hlen]; decide)
  have hg : ArmCertPipe.Guard.holds (extend inputs D_c11) (.bit 19 0 true) := hpath _ (by decide)
  simp only [ArmCertPipe.Guard.holds] at hg
  have hc : NativeR14B.tbnzBit 19#5 x = 1#1 := by
    rw [NativeR14B.tbnzBit_iff]; show (HeapV2StepCerts.RegBind.regVal x (.x ⟨19, by decide⟩)).getLsbD 0 = true; rw [hreg]; exact hg
  have hnext : (NativeR14B.tbnzTarget 6#14 x) = base + BitVec.ofNat 64 0x2b6b2c := by
    rw [NativeR14B.tbnzTarget, inv.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have hlow : (NativeR14B.tbnzTarget 6#14 x).toNat < 2 ^ 55 := by
    rw [hnext]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨fin, run, pc, vh, mem, _, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventExit real spec config rows mapping _ sc
      (referenceImageI bytes base ifunc) base cs.separated base offset_c11 budget 0 catalogue room page (by decide)
      (NativeEntryBodyDispatch.Tbnz32.selected 19#5 6#14) 1009 (fun _ => base + BitVec.ofNat 64 0x2b6b2c) x inv.core
      (ReleaseProfile.DefaultRuntimeBranch.RichTbnzTaken.tail_at real x 19#5 6#14 (by decide) hc hlow (by decide) _ hnext) nodup (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c11 _ _ mem
  have ok : (compileRun regions_c11 σ0_c11 inputs.length plan_c11).isSome = true := by rw [hall]; rfl
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 0) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, next, pc, z, dit, ev, choice⟩

#print axioms exit_c11

end ReleaseProfile.DefaultRuntime
