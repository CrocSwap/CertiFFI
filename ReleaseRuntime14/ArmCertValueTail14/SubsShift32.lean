-- ArmCertValueTail14.SubsShift32.
-- tailX = Memory's ArmCertR14Tails.SubsShift32.native_tailV + RtR14K.SubsShift32.results rewritten through its a = resSt conjunct.
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
import ArmCertR14Tails.SubsShift32
import RtR14K.SubsShift32
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ArmCertValue.R14.SubsShift32
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
open ArmCertValue.Flags

def args (Rn Rm : BitVec 5) : List Src := [.reg (.x (rk Rn)), .reg (.x (rk Rm)), .lit 1#64]
def fl (Rn Rm : BitVec 5) : VUpd × VUpd × VUpd × VUpd :=
  (⟨.sbc3N32, args Rn Rm⟩, ⟨.sbc3Z32, args Rn Rm⟩, ⟨.sbc3C32, args Rn Rm⟩, ⟨.sbc3V32, args Rn Rm⟩)

theorem h1w : ((1#1 : BitVec 1).setWidth 32) = (1#64 : BitVec 64).setWidth 32 := by decide
theorem h1n : (1#1 : BitVec 1).toNat = ((1#64 : BitVec 64).setWidth 32).toNat := by decide

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rn Rm : BitVec 5)
    (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) 31 12 == 879088#20) = false) :
    ClassTailXAt real (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) NativeEntryBodyFlag.SubsShift32.writes 17
      source (source.regs._PC + 4#64) [] (some (fl Rn Rm)) := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, hg, hs, ha⟩ :=
    ArmCertR14.RootV.SubsShift32.native_tailV real source fetched enc0 Rn Rm rn rm noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) 17
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have gEl : (actionState (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) sp 17).regs.PSTATE.EL = 0#2 := metaPins.el
  have gA64 : (actionState (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) sp 17).regs.PSTATE.nRW = 0#1 := metaPins.nrw
  have gAA : (actionState (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) sp 17).regs.FeatureImpl[4]! = true := metaPins.f4
  have gBt : (actionState (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) sp 17).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have gBn : (actionState (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) sp 17).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have RS := RtR14K.SubsShift32.results (actionState (NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) sp 17) Rn Rm rn rm gEl gA64 gAA gBt gBn (by omega) (by omega)
  dsimp only at RS
  rw [← ha] at RS
  have fN := RS.2.2.2.1
  have fZ := RS.2.2.2.2.1
  have fC := RS.2.2.2.2.2.1
  have fV := RS.2.2.2.2.2.2
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.SubsShift32.selected Rn Rm) (K := 17) post.frame
  simp only [gA] at fN fZ fC fV
  simp only [h1w, h1n] at fN fZ fC fV
  have g0 : fin.regs.gpr = fetched.regs.gpr := output.gpr.trans (hg.trans gA)
  have s0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  refine ⟨fun r => ?_, ?_, ?_, ?_, ?_⟩
  · cases r with
    | sp => simp [List.find?, regVal, s0]
    | x j => simp [List.find?, regVal, g0]
  · show (fin.regs.PSTATE.N).setWidth 64 = _
    rw [output.n, fN, b01_ofBool]; rfl
  · show (fin.regs.PSTATE.Z).setWidth 64 = _
    rw [output.zf, fZ, b01_ite]; rfl
  · show (fin.regs.PSTATE.C).setWidth 64 = _
    rw [output.c, fC, b01_ite]; rfl
  · show (fin.regs.PSTATE.V).setWidth 64 = _
    rw [output.v, fV, b01_ite]; rfl

#print axioms tailX
end ArmCertValue.R14.SubsShift32
