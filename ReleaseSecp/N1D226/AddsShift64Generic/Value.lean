import N1D226.AddsShift64Generic.AddShape
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.AddsShift64Generic.Value
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCertValue HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

def args (source : NativeState) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : List Src :=
  [.reg (.x (rk Rn)),.lit (N1D226.AddsShift64Generic.AddShape.right source imm6 Rm),.lit 0#64]
def upd (source : NativeState) (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd),some ⟨.add3,args source Rn imm6 Rm⟩)]
def flag_updates (source : NativeState) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Option (VUpd × VUpd × VUpd × VUpd) :=
  some (⟨.add3N,args source Rn imm6 Rm⟩,⟨.add3Z,args source Rn imm6 Rm⟩,
    ⟨.carry3,args source Rn imm6 Rm⟩,⟨.ovf3,args source Rn imm6 Rm⟩)

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    ClassTailXAt real (N1D226.AddsShift64Generic.Encoding.selected Rd Rn imm6 Rm) {} 15
      source (source.regs._PC+4#64) (upd source Rd Rn imm6 Rm) (flag_updates source Rn imm6 Rm) := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,np,_,gic,_⟩ :=
    N1D226.AddsShift64Generic.Tail.native_tail real source fetched enc0 Rd Rn imm6 Rm rd rn rm pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.AddsShift64Generic.Encoding.selected Rd Rn imm6 Rm) sp 15 (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.AddsShift64Generic.expected (actionState (N1D226.AddsShift64Generic.Encoding.selected Rd Rn imm6 Rm) sp 15) Rd Rn imm6 Rm).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hn,hz,hc,hv⟩ := N1D226.AddsShift64Generic.AddShape.shape
    (actionState (N1D226.AddsShift64Generic.Encoding.selected Rd Rn imm6 Rm) sp 15) Rd Rn imm6 Rm rd rn rm ap.spe
  rw [←actualRegs] at hg hs hn hz hc hv
  have gA := ActionTransport.gpr (w := N1D226.AddsShift64Generic.Encoding.selected Rd Rn imm6 Rm) (K := 15) post.frame
  simp only [N1D226.AddsShift64Generic.AddShape.flags,N1D226.AddsShift64Generic.AddShape.right,gA] at hn hz hc hv
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val
      (N1D226.AddsShift64Generic.AddShape.value fetched Rn imm6 Rm) (rk Rd).isLt := by
    rw [output.gpr,hg]
    simp only [N1D226.AddsShift64Generic.AddShape.value,N1D226.AddsShift64Generic.AddShape.right,gA]
    rfl
  have sp0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have arithmetic := N1D226.AddsShift64Generic.AddShape.flags_to_core
    fetched.regs.gpr[(GPRSummary.key Rn.toNat).val] (N1D226.AddsShift64Generic.AddShape.right fetched imm6 Rm)
  refine ⟨sp,a,fin,hook,tail,frame,q,p,sys,mem,gic,pc,np,ev,
    ValueTailE.z_tail quiet hook frame rfl np,?_⟩
  constructor
  · intro loc
    cases loc with
    | sp => simpa [upd,regVal] using sp0
    | x j =>
      by_cases h : j = rk Rd
      · rw [h]
        simp only [upd,List.find?,decide_true,Option.map_some]
        change fin.regs.gpr[(rk Rd).val] = _
        rw [gpr]
        simp only [Vector.getElem_set_self]
        unfold N1D226.AddsShift64Generic.AddShape.value N1D226.AddsShift64Generic.AddShape.Math.result
        rw [CompiledLean.CmpArithmetic.V1.result_eq]
        change fetched.regs.gpr[(rk Rn).val] + N1D226.AddsShift64Generic.AddShape.right fetched imm6 Rm + 0#64 =
          fetched.regs.gpr[(rk Rn).val] + N1D226.AddsShift64Generic.AddShape.right source imm6 Rm + 0#64
        simp only [N1D226.AddsShift64Generic.AddShape.right,input.gpr]
      · simp [upd,regVal,gpr,h,Ne.symm h,Vector.getElem_set,Fin.val_inj]
  · dsimp only [flag_updates]
    and_intros
    · change fin.regs.PSTATE.N.setWidth 64 = _
      rw [output.n,hn]
      simpa only [VUpd.eval,args,List.map,srcVal,regVal,rk,GPRSummary.key,
        N1D226.AddsShift64Generic.AddShape.Math.nzcv,N1D226.AddsShift64Generic.AddShape.right,input.gpr] using congrArg (fun t => t.1) arithmetic
    · change fin.regs.PSTATE.Z.setWidth 64 = _
      rw [output.zf,hz]
      simpa only [VUpd.eval,args,List.map,srcVal,regVal,rk,GPRSummary.key,
        N1D226.AddsShift64Generic.AddShape.Math.nzcv,N1D226.AddsShift64Generic.AddShape.right,input.gpr] using congrArg (fun t => t.2.1) arithmetic
    · change fin.regs.PSTATE.C.setWidth 64 = _
      rw [output.c,hc]
      simpa only [VUpd.eval,args,List.map,srcVal,regVal,rk,GPRSummary.key,
        N1D226.AddsShift64Generic.AddShape.Math.nzcv,N1D226.AddsShift64Generic.AddShape.right,input.gpr] using congrArg (fun t => t.2.2.1) arithmetic
    · change fin.regs.PSTATE.V.setWidth 64 = _
      rw [output.v,hv]
      simpa only [VUpd.eval,args,List.map,srcVal,regVal,rk,GPRSummary.key,
        N1D226.AddsShift64Generic.AddShape.Math.nzcv,N1D226.AddsShift64Generic.AddShape.right,input.gpr] using congrArg (fun t => t.2.2.2) arithmetic

#print axioms tailX
end N1D226.AddsShift64Generic.Value
