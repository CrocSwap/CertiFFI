import NativeEntry.Effects
import Bridge.CruxGenGuarded.BookkeepingTransport
import Bridge.CruxGenGuarded.OwnerCounterSpec
import BookkeepingGuard.GuardedBookkeepingNonProj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryInput
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- Register-only input relation. Initial memory is absent: action payloads use
the SAME actual post-fetch/walk memory and event history. No alternate state or
evaluator is constructed. Extra ControlInput transports unprojected controls.
This is internal pipeline plumbing, never a public future-state answer. -/
structure Input (s t : NativeState) : Prop where
  gpr : s.regs.gpr = t.regs.gpr
  sp : s.regs.SP_EL0 = t.regs.SP_EL0
  z : s.regs._Z = t.regs._Z
  ps : s.regs.PSTATE = t.regs.PSTATE
  sys : SysEq2 t.regs s.regs
  spx1 : s.regs.SP_EL1 = t.regs.SP_EL1
  spx2 : s.regs.SP_EL2 = t.regs.SP_EL2
  spx3 : s.regs.SP_EL3 = t.regs.SP_EL3
  el0 : s.regs.PSTATE.EL = 0#2
  pc : t.regs._PC = s.regs._PC
  controls : Effects.ControlInput s t

theorem sys_symm {a b : Regs} (h : SysEq2 a b) : SysEq2 b a where
  feat := h.feat.symm
  el := h.el.symm
  nrw := h.nrw.symm
  sctlr := h.sctlr.symm
  tcr := h.tcr.symm
  tcr2 := h.tcr2.symm
  hcr := h.hcr.symm
  scr := h.scr.symm
  mair := h.mair.symm
  mdscr := h.mdscr.symm
  httbr := h.httbr.symm
  ttbr0 := h.ttbr0.symm
  ttbr1 := h.ttbr1.symm
  hde := h.hde.symm
  tlb := h.tlb.symm
  spe := h.spe.symm
  pa := h.pa.symm

theorem of_scalar {s t : NativeState} (h : CongIn s t)
    (pc : t.regs._PC = s.regs._PC) (controls : Effects.ControlInput s t) : Input s t where
  gpr := h.gpr
  sp := h.sp
  z := h.z
  ps := h.ps
  sys := h.sys
  spx1 := h.spx1
  spx2 := h.spx2
  spx3 := h.spx3
  el0 := h.el0
  pc := pc
  controls := controls

/- Scalar memory identity is used ONLY if separately proved for that actual
domain. It is neither derived nor imposed by the new input relation. -/
theorem to_scalar {s t : NativeState} (h : Input s t)
    (mem : s.mem = t.mem) : CongIn s t where
  mem := mem
  gpr := h.gpr
  sp := h.sp
  z := h.z
  ps := h.ps
  sys := h.sys
  spx1 := h.spx1
  spx2 := h.spx2
  spx3 := h.spx3
  el0 := h.el0

theorem Input.trans {a b c : NativeState} (left : Input a b) (right : Input b c) : Input a c where
  gpr := left.gpr.trans right.gpr
  sp := left.sp.trans right.sp
  z := left.z.trans right.z
  ps := left.ps.trans right.ps
  sys := sysEq2_trans c.regs b.regs a.regs right.sys left.sys
  spx1 := left.spx1.trans right.spx1
  spx2 := left.spx2.trans right.spx2
  spx3 := left.spx3.trans right.spx3
  el0 := left.el0
  pc := right.pc.trans left.pc
  controls := left.controls.trans right.controls

theorem Input.refl (s : NativeState) (el : s.regs.PSTATE.EL = 0#2) : Input s s := by
  constructor
  all_goals first
    | exact Effects.ControlInput.refl s
    | exact el
    | rfl
    | (constructor <;> rfl)

/- ONE actual E20 successor. Its frame comes from the fixed owner theorem,
not a global ModelFrames hook or an extra public frame assumption. -/
theorem of_E20 (s t : NativeState) (frame : E20Frame s.regs t.regs)
    (el : s.regs.PSTATE.EL = 0#2) : Input s t := by
  have p := PMUFrame.of_E20 frame
  refine ⟨p.proj.1.symm, p.proj.2.1.symm, p.proj.2.2.1.symm, p.pstate.symm,
    sys_symm (e20_sys s.regs t.regs frame), p.sp1.symm, p.sp2.symm, p.sp3.symm, el,
    p.pc, ?_⟩
  exact ⟨ArmBridge.CruxNonProj.npe_of_E20 frame, p.btn⟩

/- This preserves arbitrary incoming BTYPE and BTypeNext; no StepPins0 is used.
The initial EL0 fact is part of the existing selected scalar register schema. -/
theorem at_metadata (s : NativeState) (word : BitVec 32) (K : Int)
    (el : s.regs.PSTATE.EL = 0#2) : Input s (actionState word s K) := by
  constructor
  all_goals first
    | rfl
    | exact el
    | exact ⟨BookkeepingGuard.GuardedBookkeepingNonProj.actionState_nonProj word s K, rfl⟩
    | (constructor <;> simp (disch := decide) only [actionState, RegMap.set_ne])

theorem Input.after_metadata {source current : NativeState} (input : Input source current)
    (word : BitVec 32) (K : Int) : Input source (actionState word current K) := by
  apply input.trans
  apply at_metadata
  rw [← input.ps]
  exact input.el0

theorem Input.fpcr {s t : NativeState} (input : Input s t) : t.regs.FPCR = s.regs.FPCR := by
  simpa only [ArmCertCT.CT2.mask] using congrArg Regs.FPCR input.controls.nonProj

theorem Input.fpsr {s t : NativeState} (input : Input s t) : t.regs.FPSR = s.regs.FPSR := by
  simpa only [ArmCertCT.CT2.mask] using congrArg Regs.FPSR input.controls.nonProj

/- Actual constructed spec hook followed by the EXISTING canonical metadata
state. K still must be identified by the actual native metadata boundary.
Actual fetch/walk must produce input/Q below; no fetch success is assumed at
the public boundary and no initial/current memory identity is supplied. -/
theorem after_spec_metadata (source fetched : NativeState) (input : Input source fetched)
    (ticks : Nat) (hq : HookQuiet ticks fetched) (word : BitVec 32) (K : Int) :
    ∃ sp, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      Input source (actionState word sp K) ∧ HookQuiet ticks (actionState word sp K) ∧
      (actionState word sp K).mem = fetched.mem ∧
      (actionState word sp K).events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := ArmBridge.CruxGenGuarded.Owner.spec_rule ticks fetched hq
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have derived := (input.trans (of_E20 fetched sp post.frame el)).after_metadata word K
  exact ⟨sp, hook, derived, actionState_quiet word sp K ticks post.quiet,
    (actionState_mem word sp K).trans post.mem,
    (actionState_events word sp K).trans post.events⟩

#print axioms sys_symm
#print axioms of_scalar
#print axioms to_scalar
#print axioms Input.trans
#print axioms Input.refl
#print axioms of_E20
#print axioms at_metadata
#print axioms Input.after_metadata
#print axioms Input.fpcr
#print axioms Input.fpsr
#print axioms after_spec_metadata
end NativeEntryInput
