-- ArmCertValueTail.SpMov: value tails for ADD xd, sp, #imm / MOV xd, xm (ORR xzr) /
-- SUB sp, sp, #imm / ADD sp, sp, #imm. Values straight from Core's RootV.<K>.native_tailV (already explicit);
-- NZCV frame via expected (PSTATE untouched).
import ArmCertValueTail.Def
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ArmCertValue
open HeapV2StepCerts.RegBind (Reg regVal)

/-- SP written with an op value; GPRs and NZCV unchanged. -/
theorem vholds_sp (x y : ArmBridge.Draft.NativeState) (u : VUpd) (gpr : y.regs.gpr = x.regs.gpr)
    (sp : y.regs.SP_EL0 = u.eval x) (flags : ∀ i, flagWord y i = flagWord x i) :
    VHolds [(.sp, some u)] none x y := by
  refine ⟨fun r => ?_, flags⟩
  cases r with
  | sp => simp [List.find?, regVal, sp]
  | x j => simp [List.find?, regVal, gpr]
end ArmCertValue

namespace ArmCertValue.AddSp
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)

theorem pstate (s : NativeState) (Rd : BitVec 5) (imm12 : BitVec 12) :
    (NativeEntryBody.AddSp.expected s Rd imm12).1.PSTATE = s.regs.PSTATE := by
  unfold NativeEntryBody.AddSp.expected
  try unfold NativeEntryBody.AddSp.effect_native
  rfl

def upd (Rd : BitVec 5) (imm12 : BitVec 12) : List (Reg × Option VUpd) := [(.x (rk Rd), some ⟨.add, [.reg .sp, .lit (BitVec.ofInt 64 (imm12.toNat : Int))]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddSp.selected Rd imm12) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.AddSp.Profile source) :
    ClassTailXAt real (NativeEntryBodyDispatch.AddSp.selected Rd imm12) NativeEntryBodyAdapters.AddSp.writes 18
      source (source.regs._PC + 4#64) (upd Rd imm12) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, projection, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, hg, hs, _⟩ :=
    HeapV2StepCerts.RootV.AddSp.native_tailV real source fetched enc0 Rd imm12 rd profile noEret pins input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have actualRegs : a.regs = (NativeEntryBody.AddSp.expected (actionState (NativeEntryBodyDispatch.AddSp.selected Rd imm12) sp 18) Rd imm12).1 := congrArg Prod.fst projection
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.AddSp.selected Rd imm12) (K := 18) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.AddSp.selected Rd imm12) (K := 18) post.frame
  have ps : a.regs.PSTATE = fetched.regs.PSTATE := by rw [actualRegs, pstate, pA]
  apply vholds_set1 fetched fin (rk Rd) _ (fetched.regs.SP_EL0 + BitVec.ofInt 64 (imm12.toNat : Int))
    (by rw [output.gpr, hg, gA, ActionTransport.sp0 post.frame]; try rfl) (output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))) rfl
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms tailX
end ArmCertValue.AddSp

namespace ArmCertValue.OrrMov64
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)

theorem pstate (s : NativeState) (Rd : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) :
    (NativeEntryBody.OrrMov64.expected s Rd imm6 Rm).1.PSTATE = s.regs.PSTATE := by
  unfold NativeEntryBody.OrrMov64.expected
  try unfold NativeEntryBody.OrrMov64.effect_native
  rfl

def upd (Rd : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : List (Reg × Option VUpd) := [(.x (rk Rd), some ⟨.add, [.reg (.x (rk Rm)), .lit 0#64]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) 31 12 == 879088#20) = false)
    (h6 : imm6 = 0#6) (profile : NativeEntryBodyAdapters.OrrMov64.Profile source) :
    ClassTailXAt real (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) NativeEntryBodyAdapters.OrrMov64.writes 55
      source (source.regs._PC + 4#64) (upd Rd imm6 Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, projection, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, hg, hs, _⟩ :=
    HeapV2StepCerts.RootV.OrrMov64.native_tailV real source fetched enc0 Rd imm6 Rm rd rm h6 profile noEret pins input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have actualRegs : a.regs = (NativeEntryBody.OrrMov64.expected (actionState (NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) sp 55) Rd imm6 Rm).1 := congrArg Prod.fst projection
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) (K := 55) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.OrrMov64.selected Rd imm6 Rm) (K := 55) post.frame
  have ps : a.regs.PSTATE = fetched.regs.PSTATE := by rw [actualRegs, pstate, pA]
  apply vholds_set1 fetched fin (rk Rd) _ (fetched.regs.gpr[(rk Rm).val])
    (by rw [output.gpr, hg, gA]; rfl) (output.sp.trans (hs.trans (ActionTransport.sp0 post.frame)))
    (show _ = fetched.regs.gpr[(rk Rm).val] + 0#64 from (BitVec.add_zero _).symm)
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms tailX
end ArmCertValue.OrrMov64

namespace ArmCertValue.SubSp64
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)

theorem pstate (s : NativeState) (imm12 : BitVec 12) :
    (NativeEntryBody.SubSp64.expected s imm12).1.PSTATE = s.regs.PSTATE := by
  unfold NativeEntryBody.SubSp64.expected
  try unfold NativeEntryBody.SubSp64.effect_native
  rfl

def upd (imm12 : BitVec 12) : List (Reg × Option VUpd) := [(.sp, some ⟨.add, [.reg .sp, .lit (BitVec.ofInt 64 (-(imm12.toNat : Int)))]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (imm12 : BitVec 12) 
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubSp64.selected imm12) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.SubSp64.Profile source) :
    ClassTailXAt real (NativeEntryBodyDispatch.SubSp64.selected imm12) NativeEntryBodyAdapters.SubSp64.writes 20
      source (source.regs._PC + 4#64) (upd imm12) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, projection, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, hg, hs, _⟩ :=
    HeapV2StepCerts.RootV.SubSp64.native_tailV real source fetched enc0 imm12 profile noEret pins input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have actualRegs : a.regs = (NativeEntryBody.SubSp64.expected (actionState (NativeEntryBodyDispatch.SubSp64.selected imm12) sp 20) imm12).1 := congrArg Prod.fst projection
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.SubSp64.selected imm12) (K := 20) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.SubSp64.selected imm12) (K := 20) post.frame
  have ps : a.regs.PSTATE = fetched.regs.PSTATE := by rw [actualRegs, pstate, pA]
  apply vholds_sp fetched fin _ (output.gpr.trans (hg.trans gA))
  · rw [output.sp, hs, ActionTransport.sp0 post.frame]; rfl
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms tailX
end ArmCertValue.SubSp64

namespace ArmCertValue.AddSpRestore
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)

theorem pstate (s : NativeState) (imm12 : BitVec 12) :
    (NativeEntryBody.AddSpRestore.expected s imm12).1.PSTATE = s.regs.PSTATE := by
  unfold NativeEntryBody.AddSpRestore.expected
  try unfold NativeEntryBody.AddSpRestore.effect_native
  rfl

def upd (imm12 : BitVec 12) : List (Reg × Option VUpd) := [(.sp, some ⟨.add, [.reg .sp, .lit (BitVec.ofInt 64 (imm12.toNat : Int))]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (imm12 : BitVec 12) 
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddSpRestore.selected imm12) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.AddSpRestore.Profile source) :
    ClassTailXAt real (NativeEntryBodyDispatch.AddSpRestore.selected imm12) NativeEntryBodyAdapters.AddSpRestore.writes 18
      source (source.regs._PC + 4#64) (upd imm12) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, projection, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, hg, hs, _⟩ :=
    HeapV2StepCerts.RootV.AddSpRestore.native_tailV real source fetched enc0 imm12 profile noEret pins input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have actualRegs : a.regs = (NativeEntryBody.AddSpRestore.expected (actionState (NativeEntryBodyDispatch.AddSpRestore.selected imm12) sp 18) imm12).1 := congrArg Prod.fst projection
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.AddSpRestore.selected imm12) (K := 18) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.AddSpRestore.selected imm12) (K := 18) post.frame
  have ps : a.regs.PSTATE = fetched.regs.PSTATE := by rw [actualRegs, pstate, pA]
  apply vholds_sp fetched fin _ (output.gpr.trans (hg.trans gA))
  · rw [output.sp, hs, ActionTransport.sp0 post.frame]; rfl
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms tailX
end ArmCertValue.AddSpRestore

