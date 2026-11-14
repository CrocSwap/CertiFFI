import NativeEntry.Effects
import Bridge.CruxGen
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- Class-fixed effects extend the canonical scalar action contract. This is a
register relation, not a second common execution engine. BTypeNext is an actual
output, consumed separately when establishing the next step's pins. -/
def erasePState (writes : Effects.Writes) (p : ProcState) : ProcState :=
  let q := { p with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 }
  if writes.dit then { q with DIT := 0#1 } else q

structure Frame (writes : Effects.Writes) (t u : NativeState) : Prop where
  bbool : u.regs.bank_Bool = t.regs.bank_Bool
  feat : u.regs.FeatureImpl = t.regs.FeatureImpl
  pse : erasePState writes u.regs.PSTATE = erasePState writes t.regs.PSTATE
  bt : u.regs.__BranchTaken = t.regs.__BranchTaken
  pc : u.regs._PC = t.regs._PC
  b64 : u.regs.bank_BitVec_64 = t.regs.bank_BitVec_64
  b32 : u.regs.bank_BitVec_32 = t.regs.bank_BitVec_32
  bint : u.regs.bank_Int = t.regs.bank_Int
  ss : u.regs.ShouldAdvanceSS = t.regs.ShouldAdvanceSS
  it : u.regs.ShouldAdvanceIT = t.regs.ShouldAdvanceIT
  enc : u.regs.__ThisInstrEnc = t.regs.__ThisInstrEnc
  btt : u.regs.Branchtypetaken = t.regs.Branchtypetaken
  emu : u.regs.__emulator_termination_opcode = t.regs.__emulator_termination_opcode
  b128 : u.regs.bank_BitVec_128 = t.regs.bank_BitVec_128
  nonProj : Effects.Frame writes t.regs u.regs
  gic : u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending

/- Existing scalar factories retain both their original ActFrame and NPE. -/
theorem of_scalar {t u : NativeState} (h : ActFrame t u)
    (nonProj : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs)
    (gic : u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending) :
    Frame {} t u where
  bbool := h.bbool
  feat := h.feat
  pse := by simpa [erasePState] using h.pse
  bt := h.bt
  pc := h.pc
  b64 := h.b64
  b32 := h.b32
  bint := h.bint
  ss := h.ss
  it := h.it
  enc := h.enc
  btt := h.btt
  emu := h.emu
  b128 := h.b128
  nonProj := Effects.of_scalar {} nonProj
  gic := gic

theorem to_scalar {t u : NativeState} (h : Frame {} t u)
    (next : u.regs.BTypeNext = t.regs.BTypeNext) : ActFrame t u where
  bbool := h.bbool
  feat := h.feat
  pse := by simpa [erasePState] using h.pse
  btn := next
  bt := h.bt
  pc := h.pc
  b64 := h.b64
  b32 := h.b32
  bint := h.bint
  ss := h.ss
  it := h.it
  enc := h.enc
  btt := h.btt
  emu := h.emu
  b128 := h.b128

theorem Frame.sys {writes : Effects.Writes} {t u : NativeState}
    (frame : Frame writes t u) : SysEq2 t.regs u.regs := by
  have ps_A : u.regs.PSTATE.A = t.regs.PSTATE.A := by
    have h := congrArg (fun p : ProcState => p.A) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_BTYPE : u.regs.PSTATE.BTYPE = t.regs.PSTATE.BTYPE := by
    have h := congrArg (fun p : ProcState => p.BTYPE) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_EL : u.regs.PSTATE.EL = t.regs.PSTATE.EL := by
    have h := congrArg (fun p : ProcState => p.EL) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_F : u.regs.PSTATE.F = t.regs.PSTATE.F := by
    have h := congrArg (fun p : ProcState => p.F) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_I : u.regs.PSTATE.I = t.regs.PSTATE.I := by
    have h := congrArg (fun p : ProcState => p.I) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_IL : u.regs.PSTATE.IL = t.regs.PSTATE.IL := by
    have h := congrArg (fun p : ProcState => p.IL) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_SS : u.regs.PSTATE.SS = t.regs.PSTATE.SS := by
    have h := congrArg (fun p : ProcState => p.SS) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_nRW : u.regs.PSTATE.nRW = t.regs.PSTATE.nRW := by
    have h := congrArg (fun p : ProcState => p.nRW) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  constructor <;> simp only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW]

theorem Frame.branch {writes : Effects.Writes} {t u : NativeState}
    (frame : Frame writes t u) : BrSysEq t.regs u.regs := by
  constructor <;> simp only [frame.bint, frame.b64]

/- The caller here is the internal class producer, which derives next from its
actual output. No BTN0 result is assumed at the public entry boundary. -/
theorem Frame.pins {writes : Effects.Writes} {t u : NativeState}
    (frame : Frame writes t u) (hp : StepPins t)
    (next : u.regs.BTypeNext = 0#2) : StepPins u := by
  have ps_A : u.regs.PSTATE.A = t.regs.PSTATE.A := by
    have h := congrArg (fun p : ProcState => p.A) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_BTYPE : u.regs.PSTATE.BTYPE = t.regs.PSTATE.BTYPE := by
    have h := congrArg (fun p : ProcState => p.BTYPE) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_EL : u.regs.PSTATE.EL = t.regs.PSTATE.EL := by
    have h := congrArg (fun p : ProcState => p.EL) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_F : u.regs.PSTATE.F = t.regs.PSTATE.F := by
    have h := congrArg (fun p : ProcState => p.F) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_I : u.regs.PSTATE.I = t.regs.PSTATE.I := by
    have h := congrArg (fun p : ProcState => p.I) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_IL : u.regs.PSTATE.IL = t.regs.PSTATE.IL := by
    have h := congrArg (fun p : ProcState => p.IL) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_SS : u.regs.PSTATE.SS = t.regs.PSTATE.SS := by
    have h := congrArg (fun p : ProcState => p.SS) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  have ps_nRW : u.regs.PSTATE.nRW = t.regs.PSTATE.nRW := by
    have h := congrArg (fun p : ProcState => p.nRW) frame.pse
    cases hd : writes.dit <;> simpa [erasePState, hd] using h
  constructor
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.f4
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.rme
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.spe
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.el
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.nrw
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.edecr
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.cti
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.st
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.edesr
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.btt
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.emu
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.e2h
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.tge
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.scrns
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.pmbe
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.mdss
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.pmbs
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.da
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.di
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.df
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.il
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.pss
  · simpa only [frame.bbool, frame.feat, frame.bt, frame.pc, frame.b64, frame.b32, frame.bint, frame.ss, frame.it, frame.enc, frame.btt, frame.emu, frame.b128, ps_A, ps_BTYPE, ps_EL, ps_F, ps_I, ps_IL, ps_SS, ps_nRW] using hp.btype
  · exact next

theorem Frame.dit_of_false {writes : Effects.Writes} {t u : NativeState}
    (frame : Frame writes t u) (unchanged : writes.dit = false) :
    u.regs.PSTATE.DIT = t.regs.PSTATE.DIT := by
  have h := congrArg (fun p : ProcState => p.DIT) frame.pse
  simpa [erasePState, unchanged] using h

#print axioms of_scalar
#print axioms to_scalar
#print axioms Frame.sys
#print axioms Frame.branch
#print axioms Frame.pins
#print axioms Frame.dit_of_false
end NativeEntryContract
