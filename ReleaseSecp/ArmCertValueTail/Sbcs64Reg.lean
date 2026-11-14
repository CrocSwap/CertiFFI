-- ArmCertValueTail.Sbcs64Reg (shared producer library): SBCS Xd, Xn, Xm value tail, plan row
-- (x d, ⟨sbc3, [r n, r m, F 2]⟩), fl (sbc3N, sbc3Z, sbc3C, sbc3V) on the same args.
-- tailX = Memory's ArmCertR14Tails.Sbcs64Reg.native_tailV + LRSbc.SbcsRegKey.results rewritten through a = resSt.
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
import ArmCertR14Tails.Sbcs64Reg
import LRSbc.SbcsRegKey
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCertValue.Sbcs64Reg
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
open ArmCertValue.Flags

def args (Rn Rm : BitVec 5) : List Src := [.reg (.x (rk Rn)), .reg (.x (rk Rm)), .flag 2]
def upd (Rd Rn Rm : BitVec 5) : List (Reg × Option VUpd) := [(.x (rk Rd), some ⟨.sbc3, args Rn Rm⟩)]
def fl (Rn Rm : BitVec 5) : VUpd × VUpd × VUpd × VUpd :=
  (⟨.sbc3N, args Rn Rm⟩, ⟨.sbc3Z, args Rn Rm⟩, ⟨.sbc3C, args Rn Rm⟩, ⟨.sbc3V, args Rn Rm⟩)

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    ClassTailXAt real (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) NativeEntryBodyFlag.Sbcs64Reg.writes 9
      source (source.regs._PC + 4#64) (upd Rd Rn Rm) (some (fl Rn Rm)) := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, ha⟩ :=
    ArmCertR14.RootV.Sbcs64Reg.native_tailV real source fetched enc0 Rd Rn Rm rd rn rm noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) 9
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have gEl : (actionState (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) sp 9).regs.PSTATE.EL = 0#2 := metaPins.el
  have gA64 : (actionState (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) sp 9).regs.PSTATE.nRW = 0#1 := metaPins.nrw
  have gAA : (actionState (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) sp 9).regs.FeatureImpl[4]! = true := metaPins.f4
  have gBt : (actionState (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) sp 9).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have gBn : (actionState (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) sp 9).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have RS := LRSbc.SbcsRegKey.results (actionState (NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) sp 9) Rd Rn Rm
    rd rn rm gEl gA64 gAA gBt gBn
  dsimp only at RS
  rw [← ha] at RS
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) (K := 9) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.Sbcs64Reg.selected Rd Rn Rm) (K := 9) post.frame
  have fG := RS.2.1
  have fN := RS.2.2.2.1
  have fZ := RS.2.2.2.2.1
  have fC := RS.2.2.2.2.2.1
  have fV := RS.2.2.2.2.2.2
  simp only [gA, pA] at fG fN fZ fC fV
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  apply vholds_set1_fl fetched fin (rk Rd) _ _ _ _ _ _ (output.gpr.trans fG) sp0 rfl
  · show (fin.regs.PSTATE.N).setWidth 64 = _
    rw [output.n, fN, b01_ofBool]; rfl
  · show (fin.regs.PSTATE.Z).setWidth 64 = _
    rw [output.zf, fZ, b01_ite]; rfl
  · show (fin.regs.PSTATE.C).setWidth 64 = b01 (decide (2 ^ 64 ≤ fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~fetched.regs.gpr[(GPRSummary.key Rm.toNat).val]).toNat + (fetched.regs.PSTATE.C.setWidth 64).toNat))
    rw [output.c, fC, b01_ite, toNat_c64]
  · show (fin.regs.PSTATE.V).setWidth 64 =
      b01 (decide (fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~fetched.regs.gpr[(GPRSummary.key Rm.toNat).val]).toInt + (fetched.regs.PSTATE.C.setWidth 64).toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~fetched.regs.gpr[(GPRSummary.key Rm.toNat).val]).toInt + (fetched.regs.PSTATE.C.setWidth 64).toNat))
    rw [output.v, fV, b01_ite, toNat_c64]

#print axioms tailX
end ArmCertValue.Sbcs64Reg
