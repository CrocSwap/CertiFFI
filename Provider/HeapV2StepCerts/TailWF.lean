-- Memory (B1 (c), / e01e): the NZCV frame of the epilogue's ADD sp, sp, #64 at step 356, so the TST flags
-- at 351 reach the RET state 357 (memory steps 351..355 carry it in MemRE). ClassTailWFAt = TailWE.ClassTailWAt plus
-- Flags.nzcv fin.regs = Flags.nzcv fetched.regs; tailWF_356 replaces ClassTailWAt.ofV (tailV_356) at step 356.
import HeapV2StepCerts.TailWE
import HeapV2StepCerts.RootTailVE
import HeapV2StepCerts.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace HeapV2StepCerts.TailWE
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts

/-- TailWE.ClassTailWAt plus the NZCV frame. -/
def ClassTailWFAt (real : Type) [Sail.SailReal real] (w : BitVec 32) (writes : NativeEntry.Effects.Writes)
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
      fin.events = fetched.events ∧ fin.regs._Z = fetched.regs._Z ∧
      RegBind.Holds us fetched fin ∧ ValBind.VEff k fetched fin ∧
      Flags.nzcv fin.regs = Flags.nzcv fetched.regs

variable {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int}
  {source : NativeState} {next : BitVec 64} {us us' : List (RegBind.Reg × RegBind.Upd)} {k : Nat}

theorem ClassTailWFAt.holds (e : us = us') (h : ClassTailWFAt real w writes K source next us k) :
    ClassTailWFAt real w writes K source next us' k := e ▸ h

/-- Forgetting the NZCV frame gives TailWE.ClassTailWAt. -/
theorem ClassTailWFAt.toE (h : ClassTailWFAt real w writes K source next us k) :
    ClassTailWAt real w writes K source next us k := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, _⟩ :=
    h fetched enc0 budget pins input guard quiet it ss
  exact ⟨sp, a, fin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem AddSpRestore_tailWF (source : NativeState) (imm12 : BitVec 12)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddSpRestore.selected imm12) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.AddSpRestore.Profile source) (k : Nat) (he : ValBind.effAt k = .none) :
    ClassTailWFAt real (NativeEntryBodyDispatch.AddSpRestore.selected imm12) NativeEntryBodyAdapters.AddSpRestore.writes 18 source
      (source.regs._PC + 4#64) [(.sp, .set .sp (imm12.toNat : Int))] k := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, proj, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, hg, hs, _⟩ :=
    RootV.AddSpRestore.native_tailV real source fetched enc0 imm12 profile noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have fl : Flags.nzcv fin.regs = Flags.nzcv fetched.regs := by
    have ar := congrArg Prod.fst proj
    change a.regs = _ at ar
    have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) post.frame
    simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, ar]
    exact h
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np,
    ?_, ValBind.veff_none he _ _, fl⟩
  exact RegBind.Holds.of_prefix (ActionTransport.gpr post.frame) (ActionTransport.sp0 post.frame)
    (RegBind.holds_sp _ fin (imm12.toNat : Int) (by rw [output.gpr]; exact hg) (by rw [output.sp]; exact hs))

/-- step 356 @+0xbc ADD_imm64 910103ff (AddSpRestore {'Rd': 31, 'Rn': 31, 'imm12': 64}) -/
theorem tailWF_356 (real : Type) [Sail.SailReal real] (source : ArmBridge.Draft.NativeState) :
    ClassTailWFAt real (NativeEntryBodyDispatch.AddSpRestore.selected (64#12)) NativeEntryBodyAdapters.AddSpRestore.writes 18 source
      (source.regs._PC + 4#64) (RegBind.upds 356) 356 :=
  ClassTailWFAt.holds (by decide) (AddSpRestore_tailWF (real := real) source (64#12) (by decide +kernel) ⟨⟩ 356 (by decide +kernel))

#print axioms AddSpRestore_tailWF
#print axioms tailWF_356
end HeapV2StepCerts.TailWE
