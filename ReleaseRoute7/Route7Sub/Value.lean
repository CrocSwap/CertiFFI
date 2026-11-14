-- Vendored from loops ws/LoopNative/SubImm64/Value.lean, renamed LoopNative.SubImm64 -> Route7Sub (route 7 unit 3,).
import Route7Sub.Tail
import HeapV2StepCerts.RootTailVE
import ArmCertValueTail.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace Route7Sub
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
open ArmCertValue ArmCertValue.Flags
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false

/-- Full-width subtraction in the actual decoder result. -/
theorem expected_gpr (s : NativeState) (Rd Rn : BitVec 5) (imm12 : BitVec 12)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) :
    (expected s Rd Rn imm12).1.gpr =
      s.regs.gpr.set (GPRSummary.key Rd.toNat).val
        (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64)
        (GPRSummary.key Rd.toNat).isLt := by
  have hd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hn : ¬ (Rn.toNat : Int) = 31 := by omega
  unfold expected effect_native
  simp only [hd, hn, ite_true, ite_false, dite_eq_ite, ite_self]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Functions.integer_subrange, BitVec.castWidth, Sail.get_slice_int, BitVec.extractLsb',
    BitVec.toNat_ofInt, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth, Sail.Int.toNatChecked,
    Int.toNatChecked, BitVec.toNat_ofNat, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb,
    BitVec.extractLsb, BitVec.toNat_shiftLeft]
  omega

theorem expected_sp (s : NativeState) (Rd Rn : BitVec 5) (imm12 : BitVec 12) :
    (expected s Rd Rn imm12).1.SP_EL0 = s.regs.SP_EL0 := by
  unfold expected effect_native
  rfl

theorem expected_pstate (s : NativeState) (Rd Rn : BitVec 5) (imm12 : BitVec 12) :
    (expected s Rd Rn imm12).1.PSTATE = s.regs.PSTATE := by
  unfold expected effect_native
  rfl

def upd (Rd Rn : BitVec 5) (imm12 : BitVec 12) : List (Reg × Option VUpd) :=
  [(.x (rk Rd), some ⟨.sub, [.reg (.x (rk Rn)), .lit (imm12.setWidth 64)]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn : BitVec 5) (imm12 : BitVec 12)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (Dispatch.selected Rd Rn imm12) 31 12 == 879088#20) = false) :
    ClassTailXAt real (Dispatch.selected Rd Rn imm12) Adapter.writes 20
      source (source.regs._PC + 4#64) (upd Rd Rn imm12) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, projection, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np⟩ :=
    TailCore.native_tail real source fetched enc0 Rd Rn imm12 rd rn ⟨⟩ noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have actualRegs : a.regs = (expected (actionState (Dispatch.selected Rd Rn imm12) sp 20) Rd Rn imm12).1 :=
    congrArg Prod.fst projection
  have gA := ActionTransport.gpr (w := Dispatch.selected Rd Rn imm12) (K := 20) post.frame
  have pA := ActionTransport.pstate (w := Dispatch.selected Rd Rn imm12) (K := 20) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val
      (fetched.regs.gpr[(rk Rn).val] - imm12.setWidth 64) := by
    rw [output.gpr, actualRegs, expected_gpr _ _ _ _ rd rn, gA]
    rfl
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [output.sp, actualRegs, expected_sp, ActionTransport.sp0 post.frame]
  have ps : a.regs.PSTATE = fetched.regs.PSTATE := by rw [actualRegs, expected_pstate, pA]
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev,
    ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  apply vholds_set1 fetched fin (rk Rd) _ _ gpr sp0 rfl
  exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
    (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms expected_gpr
#print axioms expected_sp
#print axioms expected_pstate
#print axioms tailX
end Route7Sub
