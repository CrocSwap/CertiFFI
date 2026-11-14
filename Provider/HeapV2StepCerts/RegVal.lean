-- Memory (target shape): value-carrying class tails at an explicit next PC.
-- ClassTailVAt = Core's ClassTailAt plus the step's register effect RegBind.Holds us fetched fin.
import HeapV2StepCerts.ValueTailDef
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace HeapV2StepCerts.RegVal
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)

def ClassTailVAt (real : Type) [Sail.SailReal real] (w : BitVec 32) (writes : NativeEntry.Effects.Writes)
    (K : Int) (source : NativeState) (next : BitVec 64) (us : List (RegBind.Reg × RegBind.Upd)) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched → MetadataGuard fetched →
    HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    ∃ sp a fin, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame writes (actionState w sp K) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      fin.mem = fetched.mem ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = next ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      RegBind.Holds us fetched fin

theorem ClassTailV.at {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes}
    {K : Int} {source : NativeState} {us : List (RegBind.Reg × RegBind.Upd)}
    (h : ValueTail.ClassTailV real w writes K source us) :
    ClassTailVAt real w writes K source (source.regs._PC + 4#64) us := h

theorem ClassTailVAt.tailAt {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes}
    {K : Int} {source : NativeState} {next : BitVec 64} {us : List (RegBind.Reg × RegBind.Upd)}
    (h : ClassTailVAt real w writes K source next us) : ClassTailAt real w writes K source next := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := h fetched enc0 budget pins input guard quiet it ss
  exact ⟨sp, a, fin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem ClassTailVAt.holds {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes}
    {K : Int} {source : NativeState} {next : BitVec 64} {us us' : List (RegBind.Reg × RegBind.Upd)}
    (e : us = us') (h : ClassTailVAt real w writes K source next us) : ClassTailVAt real w writes K source next us' :=
  e ▸ h

#print axioms ClassTailV.at
#print axioms ClassTailVAt.tailAt
end HeapV2StepCerts.RegVal
