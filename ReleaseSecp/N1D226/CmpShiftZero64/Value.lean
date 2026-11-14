import N1D226.CmpShiftZero64.CmpShape
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.CmpShiftZero64.Value
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open HeapV2StepCerts ArmCertValue
open HeapV2StepCerts.RegBind (Reg regVal rk)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] Sail.Int.toNatChecked

def upd (_Rn : BitVec 5) (_imm6 : BitVec 6) : List (Reg × Option VUpd) := []
def flag_updates (Rn : BitVec 5) (imm6 : BitVec 6) : Option (VUpd × VUpd × VUpd × VUpd) :=
  let args : List Src := [.reg (.x (rk Rn)),.lit (0#64),.lit 1#64]
  some (⟨.sbc3N,args⟩,⟨.sbc3Z,args⟩,⟨.sbc3C,args⟩,⟨.sbc3V,args⟩)

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rn : BitVec 5) (imm6 : BitVec 6) (rn : Rn.toNat < 31) :
    ClassTailXAt real (N1D226.CmpShiftZero64.Encoding.selected Rn imm6) {} 17
      source (source.regs._PC+4#64) (upd Rn imm6) (flag_updates Rn imm6) := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,np,_,gic,_⟩ :=
    N1D226.CmpShiftZero64.Tail.native_tail real source fetched enc0 Rn imm6 rn pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.CmpShiftZero64.Encoding.selected Rn imm6) sp 17
    (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.CmpShiftZero64.expected (actionState (N1D226.CmpShiftZero64.Encoding.selected Rn imm6) sp 17) Rn imm6).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hn,hz,hc,hv⟩ := N1D226.CmpShiftZero64.CmpShape.shape
    (actionState (N1D226.CmpShiftZero64.Encoding.selected Rn imm6) sp 17) Rn imm6 rn ap.spe
  rw [← actualRegs] at hg hs hn hz hc hv
  have gA := ActionTransport.gpr (w := N1D226.CmpShiftZero64.Encoding.selected Rn imm6) (K := 17) post.frame
  simp only [N1D226.CmpShiftZero64.CmpShape.flags,gA] at hn hz hc hv
  have gpr : fin.regs.gpr = fetched.regs.gpr := output.gpr.trans (hg.trans gA)
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have arithmetic := CompiledLean.CmpArithmetic.V1.flags_to_core
    fetched.regs.gpr[(GPRSummary.key Rn.toNat).val] (0#64)
  refine ⟨sp,a,fin,hook,tail,frame,q,p,sys,mem,gic,pc,np,ev,
    ValueTailE.z_tail quiet hook frame rfl np,?_⟩
  constructor
  · intro loc
    cases loc with
    | sp => exact sp0
    | x j => exact congrArg (fun g => g[j]) gpr
  · dsimp only [flag_updates]
    and_intros
    · change fin.regs.PSTATE.N.setWidth 64 = _
      rw [output.n,hn]
      simpa only [VUpd.eval,List.map,srcVal,regVal,rk,GPRSummary.key,N1D226.CmpShiftZero64.CmpShape.Math.nzcv] using congrArg (fun t => t.1) arithmetic
    · change fin.regs.PSTATE.Z.setWidth 64 = _
      rw [output.zf,hz]
      simpa only [VUpd.eval,List.map,srcVal,regVal,rk,GPRSummary.key,N1D226.CmpShiftZero64.CmpShape.Math.nzcv] using congrArg (fun t => t.2.1) arithmetic
    · change fin.regs.PSTATE.C.setWidth 64 = _
      rw [output.c,hc]
      simpa only [VUpd.eval,List.map,srcVal,regVal,rk,GPRSummary.key,N1D226.CmpShiftZero64.CmpShape.Math.nzcv] using congrArg (fun t => t.2.2.1) arithmetic
    · change fin.regs.PSTATE.V.setWidth 64 = _
      rw [output.v,hv]
      simpa only [VUpd.eval,List.map,srcVal,regVal,rk,GPRSummary.key,N1D226.CmpShiftZero64.CmpShape.Math.nzcv] using congrArg (fun t => t.2.2.2) arithmetic

#print axioms tailX
end N1D226.CmpShiftZero64.Value
