-- value tail for UMULH xd, xn, xm, certiffi table row
-- (x d, ⟨umulh, [r n, r m]⟩), fl none. From drive_spec evaluation (NativeEntryBody.Umulh64.expected)
-- through Core's RootV.Umulh64.native_tailV; no LNSym.
import ArmCertValueTail.Def
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ArmCertValue.Umulh64
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)

theorem value (s : NativeState) (Rd Rn Rm : BitVec 5) :
    (NativeEntryBody.Umulh64.expected s Rd Rn Rm).1.gpr[(GPRSummary.key Rd.toNat).val]'(GPRSummary.key Rd.toNat).isLt =
      BitVec.ofNat 64 ((s.regs.gpr[(GPRSummary.key Rn.toNat).val]'(GPRSummary.key Rn.toNat).isLt).toNat *
        (s.regs.gpr[(GPRSummary.key Rm.toNat).val]'(GPRSummary.key Rm.toNat).isLt).toNat / 2 ^ 64) := by
  unfold NativeEntryBody.Umulh64.expected NativeEntryBody.Umulh64.effect_native
  simp only [Vector.getElem_set_self]
  apply BitVec.eq_of_toNat_eq
  simp [Functions.integer_subrange, Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked,
    BitVec.extractLsb', BitVec.toNat_ofInt, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.toNat_ofNat]
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = A
  generalize s.regs.gpr[(GPRSummary.key Rm.toNat).val] = B
  have hab : A.toNat * B.toNat < 680564733841876926926749214863536422912 := by
    have h := Nat.mul_lt_mul'' A.isLt B.isLt
    simp at h
    omega
  have hm : ((A.toNat : Int) * (B.toNat : Int)) % 680564733841876926926749214863536422912 = ((A.toNat * B.toNat : Nat) : Int) := by
    rw [← Int.natCast_mul]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hab)
  rw [hm, Int.toNat_natCast, Nat.shiftRight_eq_div_pow]

theorem pstate (s : NativeState) (Rd Rn Rm : BitVec 5) :
    (NativeEntryBody.Umulh64.expected s Rd Rn Rm).1.PSTATE = s.regs.PSTATE := by
  unfold NativeEntryBody.Umulh64.expected NativeEntryBody.Umulh64.effect_native
  rfl

def upd (Rd Rn Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd), some ⟨.umulh, [.reg (.x (rk Rn)), .reg (.x (rk Rm))]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Umulh64.Profile source) :
    ClassTailXAt real (NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) NativeEntryBodyAdapters.Umulh64.writes 862
      source (source.regs._PC + 4#64) (upd Rd Rn Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, projection, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, _⟩ :=
    HeapV2StepCerts.RootV.Umulh64.native_tailV real source fetched enc0 Rd Rn Rm rd rn rm profile noEret pins input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have actualRegs : a.regs = (NativeEntryBody.Umulh64.expected
      (actionState (NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) sp 862) Rd Rn Rm).1 := congrArg Prod.fst projection
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) (K := 862) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.Umulh64.selected Rd Rn Rm) (K := 862) post.frame
  have hv : v = BitVec.ofNat 64 ((fetched.regs.gpr[(rk Rn).val]).toNat * (fetched.regs.gpr[(rk Rm).val]).toNat / 2 ^ 64) := by
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
end ArmCertValue.Umulh64
