-- Current-invariant DIT effects from the exact scalar Sail tails.
import DefaultCurrent
import RtDit4.ShimEv
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts RtDit RtDit.Shim
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapShimEffects
/-- entry_gen at a ShimInv state. -/
theorem current_gen (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (ob : FetchObligations spec config rows mapping w x) (Q : NativeState → NativeState → Prop)
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping m x final (budget - (k + 1)) →
      ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ Q final fin) :
    ∃ final fin, modelStep real x = .ok () fin ∧ final.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      final.mem = x.mem ∧ final.regs.gpr = x.regs.gpr ∧ final.regs.SP_EL0 = x.regs.SP_EL0 ∧ Q final fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  exact entry_gen real spec config rows mapping w x inv.v1.pins inv.v1.gic inv.v1.features inv.v1.debug
    (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned inv.v1.current m inv.closed inv.raw
    inv.noUpd ob Q tail

section
variable (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
include room page aligned inv

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_class"
  (← IO.getStderr).flush

/-- s0 BTI c, s1 SUB SP, s5 ISB, s8 ADD SP (any fixed-class tail not writing DIT). -/
theorem shim_class {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)}
    (tail : RegVal.ClassTailVAt real w writes K x next us) (hw : writes.dit = false)
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ fin.mem = x.mem ∧
      RegBind.Holds us x fin := by
  obtain ⟨final, fin, run, dF, mF, gF, sF, dit, mem, holds⟩ :=
    current_gen real spec config rows mapping m scope image loadBase base offset budget k catalogue room page aligned w x inv ob
      (fun final fin => fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT ∧ fin.mem = final.mem ∧ RegBind.Holds us final fin)
      (fun final enc0 f => by
        obtain ⟨sp, a, fin, hook, run, frame, _, _, _, mem, _, _, np, holds⟩ :=
          tail final enc0 _ f.pins f.input f.guard f.quiet f.it f.ss
        exact ⟨fin, run, tail_dit final sp a fin _ f.quiet hook w K frame hw np, mem, holds⟩)
  exact ⟨fin, run, dit.trans dF, mem.trans mF, RegBind.Holds.of_prefix gF sF holds⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_mrs9"
  (← IO.getStderr).flush

/-- s2 MRS X9, DIT. -/
theorem shim_mrs9 (profile : NativeEntryAdapters.MrsDit.Profile x)
    (ob : FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.gpr[9] = (0#39 +++ x.regs.PSTATE.DIT) +++ 0#24 ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ fin.mem = x.mem := by
  obtain ⟨final, fin, run, dF, mF, _, _, x9, dit, mem⟩ :=
    current_gen real spec config rows mapping m scope image loadBase base offset budget k catalogue room page aligned _ x inv ob
      (fun final fin => fin.regs.gpr[9] = (0#39 +++ final.regs.PSTATE.DIT) +++ 0#24 ∧
        fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT ∧ fin.mem = final.mem)
      (fun final enc0 f => by
        obtain ⟨fin, run, x9, dit⟩ :=
          NativeShimTails.mrsDit9_dit real x final enc0 profile f.pins f.input f.guard _ f.quiet f.it f.ss
        obtain ⟨_, _, fin2, _, run2, _, _, _, _, mem, _⟩ :=
          NativeShimTails.mrsDit9_tailVAt real x profile final enc0 _ f.pins f.input f.guard f.quiet f.it f.ss
        have e := ok_inj (real := real) run run2
        subst e
        exact ⟨fin, run, x9, dit, mem⟩)
  exact ⟨fin, run, by rw [x9, dF], dit.trans dF, mem.trans mF⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_ditOn"
  (← IO.getStderr).flush

/-- s4 MSR DIT, #1. -/
theorem shim_ditOn (profile : NativeEntryAdapters.DitOn.Profile x)
    (ob : FetchObligations spec config rows mapping NativeEntryDispatch.DitOn.word x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = 1#1 ∧ fin.mem = x.mem ∧
      RegBind.Holds [] x fin := by
  obtain ⟨final, fin, run, _, mF, gF, sF, dit, mem, holds⟩ :=
    current_gen real spec config rows mapping m scope image loadBase base offset budget k catalogue room page aligned _ x inv ob
      (fun final fin => fin.regs.PSTATE.DIT = 1#1 ∧ fin.mem = final.mem ∧ RegBind.Holds [] final fin)
      (fun final enc0 f => by
        obtain ⟨fin, run, dit⟩ :=
          NativeShimTails.ditOn_dit real x final enc0 profile f.pins f.input f.guard _ f.quiet f.it f.ss
        obtain ⟨_, _, fin2, _, run2, _, _, _, _, mem, _, _, _, holds⟩ :=
          NativeShimTails.ditOn_tailVAt real x profile final enc0 _ f.pins f.input f.guard f.quiet f.it f.ss
        have e := ok_inj (real := real) run run2
        subst e
        exact ⟨fin, run, dit, mem, holds⟩)
  exact ⟨fin, run, dit, mem.trans mF, RegBind.Holds.of_prefix gF sF holds⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Shim.shim_msr9"
  (← IO.getStderr).flush

/-- s9 MSR DIT, X9. -/
theorem shim_msr9 (profile : NativeEntryAdapters.MsrDit.Profile x)
    (ob : FetchObligations spec config rows mapping (NativeEntryDispatch.MsrDit.word 9#5) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.gpr[9].extractLsb 24 24 ∧
      fin.mem = x.mem := by
  obtain ⟨final, fin, run, _, mF, gF, _, dit, mem⟩ :=
    current_gen real spec config rows mapping m scope image loadBase base offset budget k catalogue room page aligned _ x inv ob
      (fun final fin => fin.regs.PSTATE.DIT = final.regs.gpr[9].extractLsb 24 24 ∧ fin.mem = final.mem)
      (fun final enc0 f => by
        obtain ⟨fin, run, dit⟩ :=
          NativeShimTails.msrDit9_dit real x final enc0 profile f.pins f.input f.guard _ f.quiet f.it f.ss
        obtain ⟨_, _, fin2, _, run2, _, _, _, _, mem, _⟩ :=
          NativeShimTails.msrDit9_tailVAt real x profile final enc0 _ f.pins f.input f.guard f.quiet f.it f.ss
        have e := ok_inj (real := real) run run2
        subst e
        exact ⟨fin, run, dit, mem⟩)
  exact ⟨fin, run, by rw [dit, gF], mem.trans mF⟩


end
#print axioms current_gen
#print axioms shim_class
#print axioms shim_mrs9
#print axioms shim_ditOn
#print axioms shim_msr9
end ReleaseProfile.DefaultHeapShimEffects
