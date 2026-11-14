-- ArmCertValueTail.Def (: exact shape).: value-carrying class tails for the ArmCert value layer.
-- ClassTailXAt = Memory's RegValE.ClassTailVAt with RegBind.Holds replaced by ArmCertValue.VHolds us fl
-- (certiffi Core v4/v5), over the same fetched → fin step. Generic single-write lemma vholds_set1.
import HeapV2StepCerts.RegValE
import HeapV2StepCerts.MemHolds
import ArmCertValue.Core
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace ArmCertValue
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal)

def ClassTailXAt (real : Type) [Sail.SailReal real] (w : BitVec 32) (writes : NativeEntry.Effects.Writes)
    (K : Int) (source : NativeState) (next : BitVec 64) (us : List (Reg × Option VUpd))
    (fl : Option (VUpd × VUpd × VUpd × VUpd)) : Prop :=
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
      fin.events = fetched.events ∧ fin.regs._Z = fetched.regs._Z ∧ VHolds us fl fetched fin

/-- One GPR written with an op value; everything else (other GPRs, SP, NZCV) unchanged. -/
theorem vholds_set1 (x y : NativeState) (R : Fin 31) (u : VUpd) (v : BitVec 64)
    (gpr : y.regs.gpr = x.regs.gpr.set R.val v R.isLt) (sp : y.regs.SP_EL0 = x.regs.SP_EL0)
    (hv : v = u.eval x) (flags : ∀ i, flagWord y i = flagWord x i) :
    VHolds [(.x R, some u)] none x y := by
  refine ⟨fun r => ?_, flags⟩
  cases r with
  | sp => simp [List.find?, regVal, sp]
  | x j =>
    by_cases h : R = j
    · subst h; simp [List.find?, regVal, gpr, hv]
    · have e : (Reg.x R = Reg.x j) = False := by simp [h]
      simp only [List.find?, e, decide_false, Option.map_none]
      simp only [regVal, gpr, Vector.getElem_set, Fin.val_inj]
      simp [h]

/-- NZCV words from equal PSTATE flag bits. -/
theorem flags_of {x y : NativeState} (n : y.regs.PSTATE.N = x.regs.PSTATE.N) (z : y.regs.PSTATE.Z = x.regs.PSTATE.Z)
    (c : y.regs.PSTATE.C = x.regs.PSTATE.C) (v : y.regs.PSTATE.V = x.regs.PSTATE.V) :
    ∀ i, flagWord y i = flagWord x i := by
  intro i
  rcases i with ⟨_ | _ | _ | _ | k, hk⟩
  · simp [flagWord, n]
  · simp [flagWord, z]
  · simp [flagWord, c]
  · simp [flagWord, v]
  · omega

/-- Forgetting VHolds gives Core's ClassTailAt (for the E17/CT chain). -/
theorem ClassTailXAt.tailAt {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes}
    {K : Int} {source : NativeState} {next : BitVec 64} {us : List (Reg × Option VUpd)}
    {fl : Option (VUpd × VUpd × VUpd × VUpd)}
    (h : ClassTailXAt real w writes K source next us fl) : ClassTailAt real w writes K source next := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _, _, _⟩ := h fetched enc0 budget pins input guard quiet it ss
  exact ⟨sp, a, fin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

#print axioms vholds_set1
#print axioms ClassTailXAt.tailAt
end ArmCertValue
