-- ArmCertValueTail14.AddShift64.
-- tailX = Memory's ArmCertR14Tails.AddShift64.native_tailV + RtR14K.AddShift64.results rewritten through its a = resSt conjunct.
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
import ArmCertR14Tails.AddShift64
import RtR14K.AddShift64
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ArmCertValue.R14.AddShift64
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
open ArmCertValue.Flags

def upd (Rd Rn Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd), some ⟨.add, [.reg (.x (rk Rn)), .reg (.x (rk Rm))]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (h6 : imm6 = 0#6)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddShift64.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.AddShift64.Profile source) :
    ClassTailXAt real (NativeEntryBodyDispatch.AddShift64.selected Rd Rn imm6 Rm) NativeEntryBodyAdapters.AddShift64.writes 14
      source (source.regs._PC + 4#64) (upd Rd Rn Rm) none := by
  subst h6
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, ha⟩ :=
    ArmCertR14.RootV.AddShift64.native_tailV real source fetched enc0 Rd Rn _ Rm rd rn rm profile noEret pins input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) 14
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have gEl : (actionState (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) sp 14).regs.PSTATE.EL = 0#2 := metaPins.el
  have gA64 : (actionState (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) sp 14).regs.PSTATE.nRW = 0#1 := metaPins.nrw
  have gAA : (actionState (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) sp 14).regs.FeatureImpl[4]! = true := metaPins.f4
  have gBt : (actionState (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) sp 14).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have gBn : (actionState (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) sp 14).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have RS := RtR14K.AddShift64.results (actionState (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) sp 14) Rd Rn Rm 0#6 rd rn rm gEl gA64 gAA gBt gBn
    (by omega) (by omega) (by omega)
  dsimp only at RS
  rw [← ha] at RS
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) (K := 14) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) (K := 14) post.frame
  have fG := RS.2.1
  have fN := RS.2.2.2.1
  have fZ := RS.2.2.2.2.1
  have fC := RS.2.2.2.2.2.1
  have fV := RS.2.2.2.2.2.2
  simp only [gA, pA] at fG fN fZ fC fV
  try simp only [show (0#6 : BitVec 6).toNat = 0 from rfl, BitVec.shiftLeft_zero] at fG
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  apply vholds_set1 fetched fin (rk Rd) _ _ (output.gpr.trans fG) sp0 rfl
  exact flags_of (output.n.trans fN) (output.zf.trans fZ) (output.c.trans fC) (output.v.trans fV)

#print axioms tailX
end ArmCertValue.R14.AddShift64
