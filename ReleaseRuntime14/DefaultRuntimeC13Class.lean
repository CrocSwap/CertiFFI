-- Generated current physical steps from signed c13 class rows.
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

#check "CURRENT_DECL step_c13_2"
theorem step_c13_2 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 2 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c13)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) (drawsNext : past 2 ≤ past (2 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c13 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) [] 2 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 13) (by decide) rfl
    (c := (0x8, 0x7100091f)) (by decide) offset_c13 budget 2 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.SubsImm32.selected 8#5 2#12 = BitVec.ofNat 32 (0x8, 0x7100091f).2 := by decide
  have nextPC : x.regs._PC + 4#64 = base + offset_c13 3 := by
    rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c13 2 + 4#64 = offset_c13 3 by decide]
  obtain ⟨fin, run, core, vh, hm, _, z, dit, ev, choice⟩ := ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping _ sc
    (referenceImageI bytes base ifunc) base cs.separated base offset_c13 budget 2 catalogue room page (by decide) _ _ _
    _ _ (fun y => y.regs._PC + 4#64) x inv.core
    (ArmCertValue.R14.SubsImm32.tailX real x 8#5 2#12 2#64 (by decide) (by decide) (by decide))
    (by
      apply DefaultRuntimeScalarChoice.tail_SubsImm32
      all_goals first | decide | constructor)
    nodup nextPC
    (hw ▸ ob)
  have mv := ArmCertValue.Physical.memV_nil_of_mem bytePA regions_c13 _ _ hm

  have hc : (compileRun regions_c13 σ0_c13 inputs.length plan_c13).map Prod.fst = some D_c13 := by
    rw [hlen]
    exact compiles_D_c13
  have ok : (compileRun regions_c13 σ0_c13 inputs.length plan_c13).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 2) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance (cost := 0) core next ⟨0, choice, by omega⟩ (by omega), z, dit, ev⟩

#print axioms step_c13_2

end ReleaseProfile.DefaultRuntime
