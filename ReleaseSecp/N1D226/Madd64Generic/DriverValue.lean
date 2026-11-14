import N1D226.Madd64Generic.ExprValue
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.Madd64Generic.DriverValue
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmCertValue HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

/-- Literal execution cut; the static Expr term remains the instruction value. -/
def upd (source : NativeState) (Rd Rn Ra Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd), some ⟨.orr,[.lit (Expr.eval (srcVal source) (N1D226.Madd64Generic.ExprValue.term Rn Ra Rm)),.lit 0#64]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd Rn Ra Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (ra : Ra.toNat < 31) (rm : Rm.toNat < 31) :
    ClassTailXAt real (N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm) {} 690
      source (source.regs._PC + 4#64) (upd source Rd Rn Ra Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,np,_,gic,_⟩ :=
    N1D226.Madd64Generic.Tail.native_tail real source fetched enc0 Rd Rn Ra Rm rd rn ra rm pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm) sp 690 (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.Madd64Generic.expected (actionState (N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm) sp 690) Rd Rn Ra Rm).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hp⟩ := N1D226.Madd64Generic.ExprValue.shape
    (actionState (N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm) sp 690) Rd Rn Ra Rm rd rn ra rm ap.spe
  rw [←actualRegs] at hg hs hp
  have gA := ActionTransport.gpr (w := N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm) (K := 690) post.frame
  have pA := ActionTransport.pstate (w := N1D226.Madd64Generic.Encoding.selected Rd Rn Ra Rm) (K := 690) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val
      (Expr.eval (srcVal fetched) (N1D226.Madd64Generic.ExprValue.term Rn Ra Rm)) (rk Rd).isLt := by
    rw [output.gpr,hg]
    simp only [N1D226.Madd64Generic.ExprValue.term_eval,gA]
  have sp0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have ps := hp.trans pA
  refine ⟨sp,a,fin,hook,tail,frame,q,p,sys,mem,gic,pc,np,ev,
    ValueTailE.z_tail quiet hook frame rfl np,?_⟩
  refine vholds_set1 fetched fin (rk Rd) _ _ gpr sp0 ?_ ?_
  · change Expr.eval (srcVal fetched) (N1D226.Madd64Generic.ExprValue.term Rn Ra Rm) =
      Expr.eval (srcVal source) (N1D226.Madd64Generic.ExprValue.term Rn Ra Rm) ||| 0#64
    simp only [N1D226.Madd64Generic.ExprValue.term_eval,input.gpr,BitVec.or_zero]
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms tailX
end N1D226.Madd64Generic.DriverValue
