-- Memory (B1b): the TST x1, #7 tail at step 350 with N = C = V = 0 at fin (TstF4). ClassTailWNAt =
-- TailWE.ClassTailWAt + those three; .toE forgets them; tailWN_350 replaces TailWE.tailW_350 where N/C/V are needed.
import HeapV2StepCerts.FlagTails
import HeapV2StepCerts.TailWE
import HeapV2StepCerts.FlagTailsNZCV
import HeapV2StepCerts.TailW
import HeapV2StepCerts.ValBind
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace HeapV2StepCerts.TailWE
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts

def ClassTailWNAt (real : Type) [Sail.SailReal real] (w : BitVec 32) (writes : NativeEntry.Effects.Writes)
    (K : Int) (source : NativeState) (next : BitVec 64) (us : List (RegBind.Reg × RegBind.Upd)) (k : Nat) : Prop :=
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
      fin.events = fetched.events ∧ fin.regs._Z = fetched.regs._Z ∧ RegBind.Holds us fetched fin ∧ ValBind.VEff k fetched fin ∧
      fin.regs.PSTATE.N = 0#1 ∧ fin.regs.PSTATE.C = 0#1 ∧ fin.regs.PSTATE.V = 0#1

variable {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int}
  {source : NativeState} {next : BitVec 64} {us us' : List (RegBind.Reg × RegBind.Upd)} {k : Nat}

theorem ClassTailWNAt.holds (e : us = us') (h : ClassTailWNAt real w writes K source next us k) :
    ClassTailWNAt real w writes K source next us' k := e ▸ h

theorem AndsImm0_2_tailWN (source : NativeState) (Rn : BitVec 5) (rn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 31 12 == 879088#20) = false)
    (k : Nat) (he : ValBind.effAt k = .tst (RegBind.rk Rn)) :
    ClassTailWNAt real (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) NativeEntryBodyFlag.AndsImm0_2.writes 41 source
      (source.regs._PC + 4#64) [] k := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, hg, hs, hz, hn, hc, hv⟩ :=
    FlagVN.AndsImm0_2.native_tailV real source fetched enc0 Rn rn noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  rw [ActionTransport.gpr post.frame] at hg hz
  rw [ActionTransport.sp0 post.frame] at hs
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np,
    RegBind.holds_nil _ fin (by rw [output.gpr]; exact hg) (by rw [output.sp]; exact hs), ?_,
    by rw [output.n]; exact hn, by rw [output.c]; exact hc, by rw [output.v]; exact hv⟩
  unfold ValBind.VEff; rw [he]
  show fin.regs.PSTATE.Z = 1#1 ↔ _
  rw [output.zf]; exact hz

/-- step 350 @+0xa4 ANDS_imm64 f240083f (AndsImm0_2 {'Rd': 31, 'Rn': 1}) -/
theorem tailWN_350 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWNAt real (NativeEntryBodyDispatch.AndsImm0_2.selected (1#5)) NativeEntryBodyFlag.AndsImm0_2.writes 41 source (source.regs._PC + 4#64) (RegBind.upds 350) 350 :=
  ClassTailWNAt.holds (by decide) (AndsImm0_2_tailWN (real := real) source (1#5) (by decide) (by decide +kernel) 350 (by decide +kernel))

#print axioms AndsImm0_2_tailWN
#print axioms tailWN_350
end HeapV2StepCerts.TailWE
