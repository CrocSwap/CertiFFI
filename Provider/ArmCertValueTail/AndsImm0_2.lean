-- ArmCertValueTail.AndsImm0_2: TST xn, #7 (ANDS xzr) value tail, certiffi row
-- [] / (andN [r n,#7], andZ [r n,#7], const 0, const 0). Sail facts: FlagRootsNZCV.TstF4.flags.
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
import HeapV2StepCerts.RootTailV
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace ArmCertValue.AndsImm0_2
open ArmCertValue.Flags
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryBodyAndsImm0_2
open HeapV2StepCerts


open HeapV2StepCerts.RegBind (Reg regVal rk)

def args (Rn : BitVec 5) : List Src := [.reg (.x (rk Rn)), .lit 7#64]
def fl (Rn : BitVec 5) : VUpd × VUpd × VUpd × VUpd :=
  (⟨.andN, args Rn⟩, ⟨.andZ, args Rn⟩, ⟨.const 0#64, []⟩, ⟨.const 0#64, []⟩)

theorem msb_and7 (x : BitVec 64) : (x &&& 7#64).msb = false := by
  rw [BitVec.msb_eq_getLsbD_last]; simp [BitVec.getLsbD_and]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rn : BitVec 5) (rn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 31 12 == 879088#20) = false) :
    ClassTailXAt real (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) NativeEntryBodyFlag.AndsImm0_2.writes 41
      source (source.regs._PC + 4#64) [] (some (fl Rn)) := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, hg, hs, ha⟩ :=
    HeapV2StepCerts.RootV.AndsImm0_2.native_tailV real source fetched enc0 Rn rn noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 41
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 41
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.AndsImm0_2.Guard (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) Rn := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  have e2 : ArmBridge.CruxCore.resSt (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41)) = a := ha.symm
  have RS := HeapV2StepCerts.FlagRoots.TstF4.flags (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) Rn classGuard.rn classGuard.el classGuard.a64 classGuard.aa64 classGuard.btype classGuard.btn (by have := classGuard.rn; omega)
  rw [e2] at RS
  have zf : a.regs.PSTATE.Z = (if (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).regs.gpr[(GPRSummary.key Rn.toNat).val] &&& 7#64 = 0#64 then 1#1 else 0#1) := by
    rcases ArmCertValue.Flags.bv1 a.regs.PSTATE.Z with h | h
    · rw [h]; split
      · next hc => exact absurd (RS.2.2.2.1.mpr hc) (by rw [h]; decide)
      · rfl
    · rw [h]; split
      · rfl
      · next hc => exact absurd (RS.2.2.2.1.mp h) hc
  have fN := RS.2.2.2.2.1
  have fZ := zf
  have fC := RS.2.2.2.2.2.1
  have fV := RS.2.2.2.2.2.2
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.AndsImm0_2.selected Rn) (K := 41) post.frame
  simp only [gA] at fZ
  have g0 : fin.regs.gpr = fetched.regs.gpr := output.gpr.trans (hg.trans gA)
  have s0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  refine ⟨fun r => ?_, ?_, ?_, ?_, ?_⟩
  · cases r with
    | sp => simp [List.find?, regVal, s0]
    | x j => simp [List.find?, regVal, g0]
  · show (fin.regs.PSTATE.N).setWidth 64 = b01 ((fetched.regs.gpr[(GPRSummary.key Rn.toNat).val]) &&& 7#64).msb
    rw [output.n, fN, msb_and7]; rfl
  · show (fin.regs.PSTATE.Z).setWidth 64 = b01 ((fetched.regs.gpr[(GPRSummary.key Rn.toNat).val]) &&& 7#64 == 0#64)
    rw [output.zf, fZ, b01_ite]; rfl
  · show (fin.regs.PSTATE.C).setWidth 64 = 0#64
    rw [output.c, fC]; rfl
  · show (fin.regs.PSTATE.V).setWidth 64 = 0#64
    rw [output.v, fV]; rfl

#print axioms tailX
end ArmCertValue.AndsImm0_2
