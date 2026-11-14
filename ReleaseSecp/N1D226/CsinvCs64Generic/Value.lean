import N1D226.CsinvCs64Generic.ABI
import CompiledLean.CmpArithmeticV1
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.CsinvCs64Generic.Value
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

def value (s : NativeState) (Rn Rm : BitVec 5) : BitVec 64 :=
  if s.regs.PSTATE.C = 1#1 then s.regs.gpr[(rk Rn).val] else ~~~s.regs.gpr[(rk Rm).val]

theorem shape (s : NativeState) (Rd Rn Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (spe : s.regs.bank_Bool .SPESampleInFlight = false) :
    (N1D226.CsinvCs64Generic.expected s Rd Rn Rm).1.gpr = s.regs.gpr.set (rk Rd).val (value s Rn Rm) (rk Rd).isLt ∧
    (N1D226.CsinvCs64Generic.expected s Rd Rn Rm).1.SP_EL0 = s.regs.SP_EL0 ∧
    (N1D226.CsinvCs64Generic.expected s Rd Rn Rm).1.PSTATE = s.regs.PSTATE := by
  have hd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hn : ¬ (Rn.toNat : Int) = 31 := by omega
  have hm : ¬ (Rm.toNat : Int) = 31 := by omega
  unfold N1D226.CsinvCs64Generic.expected N1D226.CsinvCs64Generic.effect_native
  simp only [hd,hn,hm,spe,ite_true,ite_false,dite_eq_ite,ite_self,ArmFull.Register.PSTATE_set]
  by_cases hc : s.regs.PSTATE.C = 1#1
  all_goals simp [value,hc,extract64,Sail.BitVec.castWidth,
    CompiledLean.CmpArithmetic.V1.full_extract,Sail.BitVec.zeroExtend,
    BitVec.zeroExtend,Int.toNatChecked,Sail.Int.toNatChecked]
  all_goals first | rfl | (split <;> rfl)

def upd (source : NativeState) (Rd Rn Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd),some ⟨.cselc 2#4,[.flag 0,.flag 1,.flag 2,.flag 3,
    .reg (.x (rk Rn)),.lit (~~~source.regs.gpr[(rk Rm).val])]⟩)]

theorem cs_eq (n z v x y : BitVec 64) (c : BitVec 1) :
    (if c = 1#1 then x else ~~~y) =
      (if condHolds 2#4 n z (c.setWidth 64) v then x else ~~~y) := by
  rcases Flags.bv1 c with rfl | rfl <;> rfl

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    ClassTailXAt real (N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm) {} 189
      source (source.regs._PC+4#64) (upd source Rd Rn Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,np,_,gic,_⟩ :=
    N1D226.CsinvCs64Generic.Tail.native_tail real source fetched enc0 Rd Rn Rm rd rn rm pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm) sp 189 (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.CsinvCs64Generic.expected (actionState (N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm) sp 189) Rd Rn Rm).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hp⟩ := shape (actionState (N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm) sp 189) Rd Rn Rm rd rn rm ap.spe
  rw [←actualRegs] at hg hs hp
  have gA := ActionTransport.gpr (w := N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm) (K := 189) post.frame
  have pA := ActionTransport.pstate (w := N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm) (K := 189) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val (value fetched Rn Rm) (rk Rd).isLt := by
    rw [output.gpr,hg]
    simp only [value,gA,pA]
  have sp0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have ps := hp.trans pA
  refine ⟨sp,a,fin,hook,tail,frame,q,p,sys,mem,gic,pc,np,ev,
    ValueTailE.z_tail quiet hook frame rfl np,?_⟩
  refine vholds_set1 fetched fin (rk Rd) _ _ gpr sp0 ?_ ?_
  · change (if fetched.regs.PSTATE.C = 1#1 then fetched.regs.gpr[(rk Rn).val] else ~~~fetched.regs.gpr[(rk Rm).val]) =
      (if condHolds 2#4 (fetched.regs.PSTATE.N.setWidth 64) (fetched.regs.PSTATE.Z.setWidth 64)
        (fetched.regs.PSTATE.C.setWidth 64) (fetched.regs.PSTATE.V.setWidth 64)
        then fetched.regs.gpr[(rk Rn).val] else ~~~source.regs.gpr[(rk Rm).val])
    rw [input.gpr]
    exact cs_eq _ _ _ _ _ _
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms shape
#print axioms tailX
end N1D226.CsinvCs64Generic.Value
