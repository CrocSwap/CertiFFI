import N1D226.CsinvCs64Generic.Tail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace N1D226.CsinvCs64Generic.ABI
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

structure Preserved (source fin : NativeState) : Prop where
  simd : fin.regs._Z = source.regs._Z
  fpcr : fin.regs.FPCR = source.regs.FPCR
  fpsr : fin.regs.FPSR = source.regs.FPSR
  tls : fin.regs.bank_BitVec_64 .TPIDR_EL0 = source.regs.bank_BitVec_64 .TPIDR_EL0

theorem of_nonProj {source fin : NativeState}
    (h : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap source.regs fin.regs) :
    Preserved source fin := by
  refine ⟨ArmBridge.CruxNonProj.fZ h,ArmBridge.CruxNonProj.fFPCR h,
    ArmBridge.CruxNonProj.fFPSR h,?_⟩
  have bank := congrFun (ArmBridge.CruxNonProj.mb64 h) .TPIDR_EL0
  simpa only [ArmCertCT.CT2.maskBank,ArmBridge.CruxNonProj.bkHeap,Bool.false_eq_true,ite_false] using bank

theorem native_abi (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (budget : Nat) (quiet : HookQuiet (budget+1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source (N1D226.CsinvCs64Generic.Encoding.selected Rd Rn Rm) enc0 fetched = .ok () fin ∧
      Preserved source fin ∧ fin.mem = fetched.mem ∧ fin.events = fetched.events ∧
      fin.regs._PC = source.regs._PC + 4#64 := by
  obtain ⟨sp,act,fin,hook,metadataInput,tail,projection,frame,q,p,sys,br,out,mem,ev,pc,np,h,gic,dit⟩ :=
    N1D226.CsinvCs64Generic.Tail.native_tail real source fetched enc0 Rd Rn Rm rd rn rm pins input guard budget quiet it ss
  exact ⟨fin,tail,of_nonProj h,mem,ev,pc⟩

#print axioms of_nonProj
#print axioms native_abi
end N1D226.CsinvCs64Generic.ABI
