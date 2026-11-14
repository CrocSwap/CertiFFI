-- value tail for MUL xd, xn, xm (MADD …, xzr), certiffi table row
-- (x d, ⟨mul, [r n, r m]⟩), fl none. From drive_spec evaluation (NativeEntryBody.Madd64.expected)
-- through Core's RootV.Madd64.native_tailV; no LNSym.
import ArmCertValueTail.Def
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ArmCertValue.Madd64
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)

theorem value (s : NativeState) (Rd Rn Rm : BitVec 5) :
    (NativeEntryBody.Madd64.expected s Rd Rn Rm).1.gpr[(GPRSummary.key Rd.toNat).val]'(GPRSummary.key Rd.toNat).isLt =
      s.regs.gpr[(GPRSummary.key Rn.toNat).val]'(GPRSummary.key Rn.toNat).isLt *
        s.regs.gpr[(GPRSummary.key Rm.toNat).val]'(GPRSummary.key Rm.toNat).isLt := by
  unfold NativeEntryBody.Madd64.expected NativeEntryBody.Madd64.effect_native
  simp only [Vector.getElem_set_self]
  apply BitVec.eq_of_toNat_eq
  simp [Functions.integer_subrange, Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked,
    BitVec.extractLsb', BitVec.toNat_ofInt, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.toNat_mul]
  omega

theorem pstate (s : NativeState) (Rd Rn Rm : BitVec 5) :
    (NativeEntryBody.Madd64.expected s Rd Rn Rm).1.PSTATE = s.regs.PSTATE := by
  unfold NativeEntryBody.Madd64.expected NativeEntryBody.Madd64.effect_native
  rfl

def upd (Rd Rn Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd), some ⟨.mul, [.reg (.x (rk Rn)), .reg (.x (rk Rm))]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Madd64.Profile source) :
    ClassTailXAt real (NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) NativeEntryBodyAdapters.Madd64.writes 690
      source (source.regs._PC + 4#64) (upd Rd Rn Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, projection, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, _⟩ :=
    HeapV2StepCerts.RootV.Madd64.native_tailV real source fetched enc0 Rd Rn Rm rd rn rm profile noEret pins input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have actualRegs : a.regs = (NativeEntryBody.Madd64.expected
      (actionState (NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) sp 690) Rd Rn Rm).1 := congrArg Prod.fst projection
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) (K := 690) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.Madd64.selected Rd Rn Rm) (K := 690) post.frame
  have hv : v = fetched.regs.gpr[(rk Rn).val] * fetched.regs.gpr[(rk Rm).val] := by
    have h1 : a.regs.gpr[(GPRSummary.key Rd.toNat).val] = v := by rw [hg]; simp
    rw [← h1, actualRegs, value, gA]; rfl
  have ps : a.regs.PSTATE = fetched.regs.PSTATE := by rw [actualRegs, pstate, pA]
  apply vholds_set1 fetched fin (rk Rd) _ v
  · rw [output.gpr, hg, gA]; rfl
  · rw [output.sp, hs, ActionTransport.sp0 post.frame]
  · rw [hv]; rfl
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms tailX
end ArmCertValue.Madd64
