import Bridge.CruxGenGuarded.EntryBodyOrrMov64Tail
import HeapV2StepCerts.RootTailVE
import ArmCertValueTail.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace LoopNative.Mov64
open NativeEntryBody.OrrMov64
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
open ArmCertValue ArmCertValue.Flags
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option maxRecDepth 1024
set_option Elab.async false

/-- MOV alias of the actual full64 ORR decoder in the actual decoder result. -/
theorem expected_gpr (s : NativeState) (Rd Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rm : Rm.toNat < 31) :
    (expected s Rd 0#6 Rm).1.gpr =
      s.regs.gpr.set (GPRSummary.key Rd.toNat).val
        (s.regs.gpr[(GPRSummary.key Rm.toNat).val])
        (GPRSummary.key Rd.toNat).isLt := by
  have hd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hn : ¬ (Rm.toNat : Int) = 31 := by omega
  have shift (v : BitVec 64) : (v <<< (0 : Int)) = v := by
    change v <<< (Int.toNat 0) = v
    simp
  unfold expected effect_native
  simp only [hd, hn, ite_true, ite_false, dite_eq_ite, ite_self]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Functions.integer_subrange, BitVec.castWidth, Sail.get_slice_int, BitVec.extractLsb',
    BitVec.toNat_ofInt, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth, Sail.Int.toNatChecked,
    Int.toNatChecked, BitVec.toNat_ofNat, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb,
    BitVec.extractLsb, BitVec.shiftLeft_zero', BitVec.shiftLeft_zero, shift]
  all_goals omega

theorem expected_sp (s : NativeState) (Rd Rm : BitVec 5) :
    (expected s Rd 0#6 Rm).1.SP_EL0 = s.regs.SP_EL0 := by
  unfold expected effect_native
  rfl

theorem expected_pstate (s : NativeState) (Rd Rm : BitVec 5) :
    (expected s Rd 0#6 Rm).1.PSTATE = s.regs.PSTATE := by
  unfold expected effect_native
  rfl

def upd (Rd Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd), some ⟨.add, [.reg (.x (rk Rm)), .lit 0]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) 31 12 == 879088#20) = false) :
    ClassTailXAt real (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) NativeEntryBodyAdapters.OrrMov64.writes 55
      source (source.regs._PC + 4#64) (upd Rd Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, projection, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyOrrMov64.native_tail real source fetched enc0 Rd 0#6 Rm rd rm ⟨⟩ noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have actualRegs : a.regs = (expected (actionState (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) sp 55) Rd 0#6 Rm).1 :=
    congrArg Prod.fst projection
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) (K := 55) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) (K := 55) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val
      (fetched.regs.gpr[(rk Rm).val]) := by
    rw [output.gpr, actualRegs, expected_gpr _ _ _ rd rm, gA]
    rfl
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [output.sp, actualRegs, expected_sp, ActionTransport.sp0 post.frame]
  have ps : a.regs.PSTATE = fetched.regs.PSTATE := by rw [actualRegs, expected_pstate, pA]
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev,
    ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  apply vholds_set1 fetched fin (rk Rd) _ _ gpr sp0 (by change _ = _ + 0#64; simp; rfl)
  exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
    (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms expected_gpr
#print axioms expected_sp
#print axioms expected_pstate
#print axioms tailX
end LoopNative.Mov64
