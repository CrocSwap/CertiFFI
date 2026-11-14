import N1D226.AdcZeroRn64Generic.ABI
import CompiledLean.CmpArithmeticV1
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.AdcZeroRn64Generic.Value
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCertValue HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] Sail.Int.toNatChecked

theorem extract64 (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x :=
  CompiledLean.CmpArithmetic.V1.full_extract x

def value (s : NativeState) (Rm : BitVec 5) : BitVec 64 :=
  CompiledLean.CmpArithmetic.V1.result 0#64 s.regs.gpr[(rk Rm).val] s.regs.PSTATE.C

theorem shape (s : NativeState) (Rd Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rm : Rm.toNat < 31)
    (spe : s.regs.bank_Bool .SPESampleInFlight = false) :
    (N1D226.AdcZeroRn64Generic.expected s Rd Rm).1.gpr = s.regs.gpr.set (rk Rd).val (value s Rm) (rk Rd).isLt ∧
    (N1D226.AdcZeroRn64Generic.expected s Rd Rm).1.SP_EL0 = s.regs.SP_EL0 ∧
    (N1D226.AdcZeroRn64Generic.expected s Rd Rm).1.PSTATE = s.regs.PSTATE := by
  have hd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hm : ¬ (Rm.toNat : Int) = 31 := by omega
  unfold N1D226.AdcZeroRn64Generic.expected N1D226.AdcZeroRn64Generic.effect_native
  simp only [hd,hm,spe,ite_true,ite_false,dite_eq_ite,ite_self,ArmFull.Register.PSTATE_set]
  and_intros
  all_goals simp [value,CompiledLean.CmpArithmetic.V1.result,extract64,Sail.BitVec.castWidth,
    CompiledLean.CmpArithmetic.V1.full_extract,Sail.BitVec.zeroExtend,
    BitVec.zeroExtend,Int.toNatChecked,Sail.Int.toNatChecked]
  all_goals rfl

def upd (Rd Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd),some ⟨.add3,[.lit 0#64,.reg (.x (rk Rm)),.flag 2]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rm : Rm.toNat < 31) :
    ClassTailXAt real (N1D226.AdcZeroRn64Generic.Encoding.selected Rd Rm) {} 6
      source (source.regs._PC+4#64) (upd Rd Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,np,_,gic,_⟩ :=
    N1D226.AdcZeroRn64Generic.Tail.native_tail real source fetched enc0 Rd Rm rd rm pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.AdcZeroRn64Generic.Encoding.selected Rd Rm) sp 6 (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.AdcZeroRn64Generic.expected (actionState (N1D226.AdcZeroRn64Generic.Encoding.selected Rd Rm) sp 6) Rd Rm).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hp⟩ := shape (actionState (N1D226.AdcZeroRn64Generic.Encoding.selected Rd Rm) sp 6) Rd Rm rd rm ap.spe
  rw [←actualRegs] at hg hs hp
  have gA := ActionTransport.gpr (w := N1D226.AdcZeroRn64Generic.Encoding.selected Rd Rm) (K := 6) post.frame
  have pA := ActionTransport.pstate (w := N1D226.AdcZeroRn64Generic.Encoding.selected Rd Rm) (K := 6) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val (value fetched Rm) (rk Rd).isLt := by
    rw [output.gpr,hg]
    simp only [value,gA,pA]
  have sp0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have ps := hp.trans pA
  refine ⟨sp,a,fin,hook,tail,frame,q,p,sys,mem,gic,pc,np,ev,
    ValueTailE.z_tail quiet hook frame rfl np,?_⟩
  refine vholds_set1 fetched fin (rk Rd) _ _ gpr sp0 ?_ ?_
  · change CompiledLean.CmpArithmetic.V1.result 0#64 fetched.regs.gpr[(rk Rm).val] fetched.regs.PSTATE.C =
      0#64 + fetched.regs.gpr[(rk Rm).val] + fetched.regs.PSTATE.C.setWidth 64
    exact CompiledLean.CmpArithmetic.V1.result_eq _ _ _
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms shape
#print axioms tailX
end N1D226.AdcZeroRn64Generic.Value
