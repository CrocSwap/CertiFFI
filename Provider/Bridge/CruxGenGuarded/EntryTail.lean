import Bridge.CruxGenGuarded.EntryEpilogue
import Bridge.CruxGenGuarded.OwnerHooks
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.guarded_after_action_current"
  (← IO.getStderr).flush

theorem guarded_after_action_current (real : Type) [Sail.SailReal real]
    (initial : NativeState) (w : BitVec 32) (enc0 : __InstrEnc)
    (a : NativeState) (b : Nat) (hq : HookQuiet (b + 1) a) (hp : EntryPins a)
    (hEnc : a.regs.__ThisInstrEnc = .__A64)
    (hEret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
    (hIT : a.regs.ShouldAdvanceIT = false) (hSS : a.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeAfterAction real initial w enc0 a = .ok () fin ∧
      HookQuiet b fin ∧ EntryPins fin ∧
      fin.regs.PSTATE.BTYPE = a.regs.BTypeNext ∧ fin.regs.BTypeNext = a.regs.BTypeNext ∧
      SysEq2 a.regs fin.regs ∧
      BrSysEq a.regs fin.regs ∧ CongOut fin a ∧ fin.events = a.events ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.PSTATE.DIT = a.regs.PSTATE.DIT ∧
      fin.regs._PC = (if a.regs.__BranchTaken then a.regs._PC else a.regs._PC + 4#64) ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs := by
  obtain ⟨r, hr, pr⟩ := Owner.hook_laws.retired (b + 1) a hq
  have fr := PMUFrame.of_E20 pr.frame
  have hpr := NativeEntryTail.EntryPins.after_E20 a r hp pr.frame
  have hEncR : r.regs.__ThisInstrEnc = .__A64 := fr.enc.trans hEnc
  have hEretR : (Sail.BitVec.extractLsb (r.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [fr.thisInstr]; exact hEret
  have hepi := epilogue_current_boundary real r hpr hEncR hEretR (fr.it.trans hIT) (fr.ss.trans hSS)
  have hpc := beforeCounterCurrent_pins r hpr
  obtain ⟨c, hc, pc⟩ := Owner.hook_laws.counter b (beforeCounterCurrent r) (beforeCounterCurrent_quiet (b + 1) r pr.quiet)
  have hpc' := entry_after_E22 (beforeCounterCurrent r) c hpc pc.frame
  have hcnt := counter_boundary real (beforeCounterCurrent r) c hc hpc'.f4 hpc'.nrw
  obtain ⟨p, hcy, pp⟩ := Owner.hook_laws.cycle b c pc.quiet
  have hpp := NativeEntryTail.EntryPins.after_E20 c p hpc' pp.frame
  have hend := cycle_boundary real c p hcy
  refine ⟨nativeEndState p, ?_, nativeEndState_quiet b p pp.quiet,
    entry_after_end p hpp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      nativeAfterAction real initial w enc0 a = nativeAfterRetired r :=
        retired_pmu_boundary real initial w enc0 a r hr
      _ = nativeAtCounter (beforeCounterCurrent r) := hepi
      _ = nativeAtPmuCycle c := hcnt
      _ = .ok () (nativeEndState p) := hend
  · change p.regs.PSTATE.BTYPE = a.regs.BTypeNext
    exact (congrArg ProcState.BTYPE (PMUFrame.of_E20 pp.frame).pstate).trans
      ((congrArg ProcState.BTYPE (PMUFrame.of_E22 pc.frame).pstate).trans
        ((beforeCounterCurrent_btype r).trans fr.btn))
  · change p.regs.BTypeNext = a.regs.BTypeNext
    exact (PMUFrame.of_E20 pp.frame).btn.trans
      ((PMUFrame.of_E22 pc.frame).btn.trans ((beforeCounterCurrent_btn r).trans fr.btn))
  · exact sysEq2_trans _ _ _ (e20_sys _ _ pr.frame)
      (sysEq2_trans _ _ _ (beforeCounterCurrent_sys r hpr)
        (sysEq2_trans _ _ _ (e22_sys _ _ pc.frame)
          (sysEq2_trans _ _ _ (e20_sys _ _ pp.frame) (end_sys p))))
  · exact brSysEq_trans _ _ _ (e20_branch _ _ pr.frame)
      (brSysEq_trans _ _ _ (beforeCounterCurrent_branch r)
        (brSysEq_trans _ _ _ (e22_branch _ _ pc.frame)
          (brSysEq_trans _ _ _ (e20_branch _ _ pp.frame) (end_branch p))))
  · exact congOut_trans _ _ _ (nativeEndState_cong p)
      (congOut_trans _ _ _ (e20_output c p pp.frame pp.mem)
        (congOut_trans _ _ _ (e22_output (beforeCounterCurrent r) c pc.frame pc.mem)
          (congOut_trans _ _ _ (beforeCounterCurrent_output r) (e20_output a r pr.frame pr.mem))))
  · exact (nativeEndState_events p).trans (pp.events.trans
      (pc.events.trans ((beforeCounterCurrent_events r).trans pr.events)))
  · exact pp.gic.trans (pc.gic.trans ((beforeCounterCurrent_gic r).trans pr.gic))
  · exact (congrArg ProcState.DIT (PMUFrame.of_E20 pp.frame).pstate).trans
      ((congrArg ProcState.DIT (PMUFrame.of_E22 pc.frame).pstate).trans
        ((beforeCounterCurrent_dit r).trans (congrArg ProcState.DIT fr.pstate)))
  · have fc := PMUFrame.of_E22 pc.frame
    have fp := PMUFrame.of_E20 pp.frame
    calc
      (nativeEndState p).regs._PC = p.regs._PC := nativeEndState_pc p
      _ = c.regs._PC := fp.pc
      _ = (beforeCounterCurrent r).regs._PC := fc.pc
      _ = (if r.regs.__BranchTaken then r.regs._PC else r.regs._PC + 4#64) := beforeCounterCurrent_pc r
      _ = (if a.regs.__BranchTaken then a.regs._PC else a.regs._PC + 4#64) := by rw [fr.bt, fr.pc]
  · exact Eq.trans (BookkeepingGuard.GuardedBookkeepingNonProj.nativeEndState_nonProj p)
      (Eq.trans (ArmBridge.CruxNonProj.npe_of_E20 pp.frame)
        (Eq.trans (ArmBridge.CruxNonProj.npe_of_E22 pc.frame)
          (Eq.trans (beforeCounterCurrent_nonProj r hpr) (ArmBridge.CruxNonProj.npe_of_E20 pr.frame))))


/- Legacy zero-case signature used by the six current callee joins. -/
theorem guarded_after_action_entry (real : Type) [Sail.SailReal real]
    (initial : NativeState) (w : BitVec 32) (enc0 : __InstrEnc)
    (a : NativeState) (b : Nat) (hq : HookQuiet (b + 1) a) (hp : EntryPins a)
    (next : a.regs.BTypeNext = 0#2)
    (hEnc : a.regs.__ThisInstrEnc = .__A64)
    (hEret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
    (hIT : a.regs.ShouldAdvanceIT = false) (hSS : a.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeAfterAction real initial w enc0 a = .ok () fin ∧
      HookQuiet b fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      BrSysEq a.regs fin.regs ∧ CongOut fin a ∧ fin.events = a.events ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.PSTATE.DIT = a.regs.PSTATE.DIT ∧
      fin.regs._PC = (if a.regs.__BranchTaken then a.regs._PC else a.regs._PC + 4#64) ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs := by
  obtain ⟨fin, action, quiet, pins, btype, btn, rest⟩ :=
    guarded_after_action_current real initial w enc0 a b hq hp hEnc hEret hIT hSS
  exact ⟨fin, action, quiet, scalar_pins fin pins (btype.trans next) (btn.trans next), rest⟩

#print axioms guarded_after_action_current
#print axioms guarded_after_action_entry
end ArmBridge.CruxGenGuarded
