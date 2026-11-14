-- Memory (certiffi (c2)): ClassTail plus the step's register effect (RegBind.Holds) — the value-carrying
-- class-tail predicate the body value tails (RootTailV / FlagRootV) prove.
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.ActionTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace HeapV2StepCerts.ValueTail
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)

/-- ClassTail plus the step's register effect on GPRs / SP (for the RegBind carry). -/
def ClassTailV (real : Type) [Sail.SailReal real] (w : BitVec 32) (writes : NativeEntry.Effects.Writes)
    (K : Int) (source : NativeState) (us : List (RegBind.Reg × RegBind.Upd)) : Prop :=
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
      fin.regs._PC = source.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      RegBind.Holds us fetched fin

theorem ClassTailV.tail {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes}
    {K : Int} {source : NativeState} {us : List (RegBind.Reg × RegBind.Upd)} (h : ClassTailV real w writes K source us) :
    ClassTail real w writes K source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := h fetched enc0 budget pins input guard quiet it ss
  exact ⟨sp, a, fin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end HeapV2StepCerts.ValueTail
