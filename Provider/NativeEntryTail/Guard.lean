import NativeEntryContract.Core
import Bridge.CruxGenGuarded.UniformEpilogue
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryTail
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- Actual input controls; neither incoming BTYPE nor BTN is restricted. -/
structure EntryPins (s : NativeState) : Prop where
  f4 : s.regs.FeatureImpl[4]! = true
  rme : s.regs.FeatureImpl[232]! = false
  spe : s.regs.bank_Bool .SPESampleInFlight = false
  el : s.regs.PSTATE.EL = 0#2
  nrw : s.regs.PSTATE.nRW = 0#1
  edecr : _get_EDECR_Type_RCE (s.regs.bank_BitVec_32 .EDECR) = 0#1
  cti : _get_CTIDEVCTL_Type_RCE (s.regs.bank_BitVec_32 .CTIDEVCTL) = 0#1
  st : _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6
  edesr : s.regs.bank_BitVec_32 .EDESR = 0#32
  btt : s.regs.Branchtypetaken ≠ BranchType.BranchType_RESET
  emu : s.regs.__emulator_termination_opcode = none
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  scrns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  pmbe : _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1
  mdss : _get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1
  pmbs : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1
  da : s.regs.PSTATE.A = 0#1
  di : s.regs.PSTATE.I = 0#1
  df : s.regs.PSTATE.F = 0#1
  il : s.regs.PSTATE.IL = 0#1
  pss : s.regs.PSTATE.SS = 0#1

structure TailGuard (s : NativeState) : Prop where
  f4 : s.regs.FeatureImpl[4]! = true
  rme : s.regs.FeatureImpl[232]! = false
  spe : s.regs.bank_Bool .SPESampleInFlight = false
  el : s.regs.PSTATE.EL = 0#2
  nrw : s.regs.PSTATE.nRW = 0#1
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  scrns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  pmbe : _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1
  mdss : _get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1
  pmbs : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1
  pss : s.regs.PSTATE.SS = 0#1
  btn : s.regs.BTypeNext = 0#2

theorem EntryPins.of_scalar (s : NativeState) (hp : StepPins s) : EntryPins s where
  f4 := hp.f4
  rme := hp.rme
  spe := hp.spe
  el := hp.el
  nrw := hp.nrw
  edecr := hp.edecr
  cti := hp.cti
  st := hp.st
  edesr := hp.edesr
  btt := hp.btt
  emu := hp.emu
  e2h := hp.e2h
  tge := hp.tge
  scrns := hp.scrns
  pmbe := hp.pmbe
  mdss := hp.mdss
  pmbs := hp.pmbs
  da := hp.da
  di := hp.di
  df := hp.df
  il := hp.il
  pss := hp.pss

theorem EntryPins.after_action {writes : NativeEntry.Effects.Writes} {t u : NativeState}
    (frame : NativeEntryContract.Frame writes t u) (hp : EntryPins t) : EntryPins u := by
  have ps_A : u.regs.PSTATE.A = t.regs.PSTATE.A := by
    have h := congrArg (fun p : ProcState => p.A) frame.pse
    cases hd : writes.dit <;> simpa [NativeEntryContract.erasePState, hd] using h
  have ps_BTYPE : u.regs.PSTATE.BTYPE = t.regs.PSTATE.BTYPE := by
    have h := congrArg (fun p : ProcState => p.BTYPE) frame.pse
    cases hd : writes.dit <;> simpa [NativeEntryContract.erasePState, hd] using h
  have ps_EL : u.regs.PSTATE.EL = t.regs.PSTATE.EL := by
    have h := congrArg (fun p : ProcState => p.EL) frame.pse
    cases hd : writes.dit <;> simpa [NativeEntryContract.erasePState, hd] using h
  have ps_F : u.regs.PSTATE.F = t.regs.PSTATE.F := by
    have h := congrArg (fun p : ProcState => p.F) frame.pse
    cases hd : writes.dit <;> simpa [NativeEntryContract.erasePState, hd] using h
  have ps_I : u.regs.PSTATE.I = t.regs.PSTATE.I := by
    have h := congrArg (fun p : ProcState => p.I) frame.pse
    cases hd : writes.dit <;> simpa [NativeEntryContract.erasePState, hd] using h
  have ps_IL : u.regs.PSTATE.IL = t.regs.PSTATE.IL := by
    have h := congrArg (fun p : ProcState => p.IL) frame.pse
    cases hd : writes.dit <;> simpa [NativeEntryContract.erasePState, hd] using h
  have ps_SS : u.regs.PSTATE.SS = t.regs.PSTATE.SS := by
    have h := congrArg (fun p : ProcState => p.SS) frame.pse
    cases hd : writes.dit <;> simpa [NativeEntryContract.erasePState, hd] using h
  have ps_nRW : u.regs.PSTATE.nRW = t.regs.PSTATE.nRW := by
    have h := congrArg (fun p : ProcState => p.nRW) frame.pse
    cases hd : writes.dit <;> simpa [NativeEntryContract.erasePState, hd] using h
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

theorem TailGuard.of_entry (s : NativeState) (hp : EntryPins s) (next : s.regs.BTypeNext = 0#2) : TailGuard s where
  f4 := hp.f4
  rme := hp.rme
  spe := hp.spe
  el := hp.el
  nrw := hp.nrw
  e2h := hp.e2h
  tge := hp.tge
  scrns := hp.scrns
  pmbe := hp.pmbe
  mdss := hp.mdss
  pmbs := hp.pmbs
  pss := hp.pss
  btn := next

theorem EntryPins.after_E20 (s t : NativeState) (hp : EntryPins s) (hE : E20Frame s.regs t.regs) : EntryPins t := by
  constructor
  · have hf := frame_pres_E20 (fun x : Regs => x.FeatureImpl[4]! = true)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.f4
  · have hf := frame_pres_E20 (fun x : Regs => x.FeatureImpl[232]! = false)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.rme
  · have hf := frame_pres_E20 (fun x : Regs => x.bank_Bool .SPESampleInFlight = false)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.spe
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.EL = 0#2)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.el
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.nRW = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.nrw
  · have hf := frame_pres_E20 (fun x : Regs => _get_EDECR_Type_RCE (x.bank_BitVec_32 .EDECR) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.edecr
  · have hf := frame_pres_E20 (fun x : Regs => _get_CTIDEVCTL_Type_RCE (x.bank_BitVec_32 .CTIDEVCTL) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.cti
  · have hf := frame_pres_E20 (fun x : Regs => _get_EDSCR_Type_STATUS (x.bank_BitVec_32 ._EDSCR) = 0b000010#6)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.st
  · have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_32 .EDESR = 0#32)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.edesr
  · have hf := frame_pres_E20 (fun x : Regs => x.Branchtypetaken ≠ BranchType.BranchType_RESET)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.btt
  · have hf := frame_pres_E20 (fun x : Regs => x.__emulator_termination_opcode = none)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.emu
  · have hf := frame_pres_E20 (fun x : Regs => _get_HCR_EL2_Type_E2H (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.e2h
  · have hf := frame_pres_E20 (fun x : Regs => _get_HCR_EL2_Type_TGE (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.tge
  · have hf := frame_pres_E20 (fun x : Regs => _get_SCR_EL3_Type_NS (x.bank_BitVec_64 .SCR_EL3) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.scrns
  · have hf := frame_pres_E20 (fun x : Regs => _get_PMBLIMITR_EL1_Type_E (x.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.pmbe
  · have hf := frame_pres_E20 (fun x : Regs => _get_MDSCR_EL1_Type_SS (x.bank_BitVec_64 .MDSCR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.mdss
  · have hf := frame_pres_E20 (fun x : Regs => Sail.BitVec.extractLsb (x.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.pmbs
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.A = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.da
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.I = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.di
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.F = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.df
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.IL = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.il
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.SS = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.pss

theorem TailGuard.after_E20 (s t : NativeState) (hp : TailGuard s) (hE : E20Frame s.regs t.regs) : TailGuard t := by
  constructor
  · have hf := frame_pres_E20 (fun x : Regs => x.FeatureImpl[4]! = true)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.f4
  · have hf := frame_pres_E20 (fun x : Regs => x.FeatureImpl[232]! = false)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.rme
  · have hf := frame_pres_E20 (fun x : Regs => x.bank_Bool .SPESampleInFlight = false)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.spe
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.EL = 0#2)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.el
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.nRW = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.nrw
  · have hf := frame_pres_E20 (fun x : Regs => _get_HCR_EL2_Type_E2H (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.e2h
  · have hf := frame_pres_E20 (fun x : Regs => _get_HCR_EL2_Type_TGE (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.tge
  · have hf := frame_pres_E20 (fun x : Regs => _get_SCR_EL3_Type_NS (x.bank_BitVec_64 .SCR_EL3) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.scrns
  · have hf := frame_pres_E20 (fun x : Regs => _get_PMBLIMITR_EL1_Type_E (x.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.pmbe
  · have hf := frame_pres_E20 (fun x : Regs => _get_MDSCR_EL1_Type_SS (x.bank_BitVec_64 .MDSCR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.mdss
  · have hf := frame_pres_E20 (fun x : Regs => Sail.BitVec.extractLsb (x.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.pmbs
  · have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.SS = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.pss
  · have hf := frame_pres_E20 (fun x : Regs => x.BTypeNext = 0#2)
      (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) hE
    exact hf.mpr hp.btn

#print axioms EntryPins.of_scalar
#print axioms EntryPins.after_action
#print axioms TailGuard.of_entry
#print axioms EntryPins.after_E20
#print axioms TailGuard.after_E20
end NativeEntryTail
