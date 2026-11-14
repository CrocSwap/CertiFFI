-- (H-P4): DIT converters for the branch-class steps (CBZ / B.cond / RET via the actual native
-- tails, ActFrameBr + NonProj) and BL (CallerBl's bl_action_tail exports DIT across the action).
import RtDit.Base
import RtBranch.BranchStepV3Classes
import RtBl.BlStepV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded NativeEntryCallerParts NativeEntryCallerTransport
open ArmBridge.CruxGenGuarded.CallerBl
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace RtDit

theorem frameBr_dit {t u : NativeState} (h : ArmBridge.CruxGenBr.ActFrameBr t u) :
    u.regs.PSTATE.DIT = t.regs.PSTATE.DIT := by
  have e := congrArg ProcState.DIT h.pse
  simpa using e

theorem tailBr_dit (fetched sp a fin : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp) (w : BitVec 32) (K : Int)
    (frame : ArmBridge.CruxGenBr.ActFrameBr (actionState w sp K) a)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    fin.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT :=
  (np_dit np).trans ((frameBr_dit frame).trans ((action_dit w sp K).trans (e20_dit fetched sp budget quiet hook)))

theorem dit_cbz (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {s : NativeState}
    (Rt : BitVec 5) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyCbz.W Rt imm19) 31 12 == 879088#20) = false)
    (stepPins : StepPins s) (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s (EntryBodyCbz.W Rt imm19) enc0 final = .ok () fin ∧
        fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have bpF := EntryFetchedBranch.fetched_branch_pins acc nx s final stepPins hregs bp
  obtain ⟨sp, a, fin, pmu, run, frame, _, _, _, _, _, _, _, _, _, _, np, _⟩ :=
    EntryBodyCbz.native_tail_x real s final enc0 Rt imm19 noEret f.pins bpF f.input f.guard budget f.quiet f.it f.ss hlow
  exact ⟨fin, run, tailBr_dit final sp a fin budget f.quiet pmu _ _ frame np⟩

theorem dit_bcond (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {s : NativeState}
    (cond : BitVec 4) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyBcond.W cond imm19) 31 12 == 879088#20) = false)
    (stepPins : StepPins s) (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s (EntryBodyBcond.W cond imm19) enc0 final = .ok () fin ∧
        fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have bpF := EntryFetchedBranch.fetched_branch_pins acc nx s final stepPins hregs bp
  obtain ⟨sp, a, fin, pmu, run, frame, _, _, _, _, _, _, _, _, _, _, np, _⟩ :=
    EntryBodyBcond.native_tail_x real s final enc0 cond imm19 noEret f.pins bpF f.input f.guard budget f.quiet f.it f.ss hlow
  exact ⟨fin, run, tailBr_dit final sp a fin budget f.quiet pmu _ _ frame np⟩

theorem dit_ret (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {s : NativeState}
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (stepPins : StepPins s) (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (hlow : (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s (EntryBodyRet.W Rn) enc0 final = .ok () fin ∧
        fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have bpF := EntryFetchedBranch.fetched_branch_pins acc nx s final stepPins hregs bp
  obtain ⟨sp, a, fin, pmu, run, frame, _, _, _, _, _, _, _, _, _, _, np, _⟩ :=
    EntryBodyRet.native_tail_x real s final enc0 Rn hRn noEret f.pins bpF f.input f.guard budget f.quiet f.it f.ss hlow
  exact ⟨fin, run, tailBr_dit final sp a fin budget f.quiet pmu _ _ frame np⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.dit_bl"
  (← IO.getStderr).flush

theorem dit_bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {s : NativeState}
    (imm26 : BitVec 26) (controls : CallerControls s) (low : (blTarget imm26 s).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s (NativeEntryCallerDispatch.Bl.word imm26) enc0 final = .ok () fin ∧
        fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have sysF : SysEq2 s.regs final.regs := EntryBranchPins.sysEq2_symm _ _ f.input.sys
  have controlsF := HeapV2StepCerts.BlStepV3.caller_controls_fetched s final hregs sysF controls
  have pinsE : EntryPins final := NativeEntryTail.EntryPins.of_scalar final f.pins
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) final f.quiet
  have ps := NativeEntryTail.EntryPins.after_E20 final sp pinsE post.frame
  have pc := caller_controls_after_E20 final sp controlsF post.frame
  let a := actionState (NativeEntryCallerDispatch.Bl.word imm26) sp 68
  have ca : CallerControls a := caller_controls_at_metadata sp (NativeEntryCallerDispatch.Bl.word imm26) 68 pc
  have pa : EntryPins a := entryPins_at_metadata sp (NativeEntryCallerDispatch.Bl.word imm26) 68 ps
  have qa : HookQuiet (budget + 1) a := actionState_quiet (NativeEntryCallerDispatch.Bl.word imm26) sp 68 (budget + 1) post.quiet
  have target : blTarget imm26 a = blTarget imm26 s := by
    rw [NativeEntryCallerRegisters.bl_target, NativeEntryCallerRegisters.bl_target]
    change sp.regs._PC + _ = s.regs._PC + _
    rw [(PMUFrame.of_E20 post.frame).pc, f.input.pc]
  have lowA : (blTarget imm26 a).toNat < 2^55 := by rw [target]; exact low
  have encA : a.regs.__ThisInstrEnc = .__A64 := by rfl
  have eretA : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false :=
    word_not_eret imm26
  have itA : a.regs.ShouldAdvanceIT = false := (PMUFrame.of_E20 post.frame).it.trans f.it
  have ssA : a.regs.ShouldAdvanceSS = true := (PMUFrame.of_E20 post.frame).ss.trans f.ss
  have dispatch : DispatchAt real (NativeEntryCallerDispatch.Bl.word imm26) (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) 68 := by
    intro pc t see
    exact NativeEntryCallerDispatch.Bl.dispatch_at real pc imm26 t (by simpa using see)
  have metadataBoundary := metadata_boundary_at real s (NativeEntryCallerDispatch.Bl.word imm26) (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) enc0 sp
    (f.guard.after_E20 post.frame) 68 (by decide) dispatch
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, dit, _⟩ :=
    bl_action_tail real s (NativeEntryCallerDispatch.Bl.word imm26) enc0 imm26 a budget ca lowA qa pa encA eretA itA ssA
  refine ⟨fin, (spec_pmu_boundary real s (NativeEntryCallerDispatch.Bl.word imm26) enc0 final sp hook).trans (metadataBoundary.trans run), ?_⟩
  rw [dit]
  show sp.regs.PSTATE.DIT = _
  exact frame_pres_E20 (fun x => x.PSTATE.DIT) (fun x => by simp only [eraseE20]) post.frame

#print axioms frameBr_dit
#print axioms dit_cbz
#print axioms dit_bcond
#print axioms dit_ret
#print axioms dit_bl
end RtDit
