import N1D226.SubShiftBorrow.ABI
import ArmCertValue.ExprStep
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.SubShiftBorrow.ExprValue
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmCertValue HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] Sail.Int.toNatChecked

def term (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Expr.Term := .binary .sub (.source (.reg (.x (rk Rn)))) (.unary (.lsl imm6.toNat) (.source (.reg (.x (rk Rm)))))

theorem term_eval (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Expr.eval (srcVal s) (term Rd Rn imm6 Rm) = s.regs.gpr[(GPRSummary.key Rn.toNat).val] - (s.regs.gpr[(GPRSummary.key Rm.toNat).val] <<< imm6.toNat) := rfl

theorem full_extract (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb,BitVec.extractLsb,Int.toNatChecked]

theorem shift_nat (x : BitVec 64) (n : Nat) : x <<< (n : Int) = x <<< n := by
  simp [Sail.instHShiftLeftBitVecInt_sail]

theorem shape (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (spe : s.regs.bank_Bool .SPESampleInFlight = false) :
    (N1D226.SubShiftBorrow.expected s Rd Rn imm6 Rm).1.gpr = s.regs.gpr.set (rk Rd).val
      (Expr.eval (srcVal s) (term Rd Rn imm6 Rm)) (rk Rd).isLt ∧
    (N1D226.SubShiftBorrow.expected s Rd Rn imm6 Rm).1.SP_EL0 = s.regs.SP_EL0 ∧
    (N1D226.SubShiftBorrow.expected s Rd Rn imm6 Rm).1.PSTATE = s.regs.PSTATE := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hRn : ¬ (Rn.toNat : Int) = 31 := by omega
  have hRm : ¬ (Rm.toNat : Int) = 31 := by omega
  unfold N1D226.SubShiftBorrow.expected N1D226.SubShiftBorrow.effect_native
  simp only [hRd,hRn,hRm,spe,ite_true,ite_false,dite_eq_ite,ite_self]
  refine ⟨?_,by first | trivial | rfl,by first | trivial | rfl⟩
  · rw [term_eval]
    congr 1
    simp only [shift_nat]
    apply BitVec.eq_of_toNat_eq
    simp [Functions.integer_subrange,BitVec.castWidth,Sail.get_slice_int,BitVec.extractLsb',
      BitVec.toNat_ofInt,BitVec.toNat_add,BitVec.toNat_sub,BitVec.toNat_setWidth,
      Sail.Int.toNatChecked,Int.toNatChecked,BitVec.toNat_ofNat,Sail.BitVec.zeroExtend,
      Sail.BitVec.extractLsb,BitVec.extractLsb,BitVec.toNat_shiftLeft,shift_nat,Sail.instHShiftLeftBitVecInt_sail]
    omega

theorem output_one (x y : NativeState) (r : Fin 31) (e : Expr.Term)
    (gpr : y.regs.gpr = x.regs.gpr.set r.val (Expr.eval (srcVal x) e) r.isLt)
    (sp : y.regs.SP_EL0 = x.regs.SP_EL0) (fl : ∀ i, flagWord y i = flagWord x i) :
    Expr.OutputHolds [(.reg (.x r),e)] x y := by
  constructor
  · intro loc term member
    simp only [List.mem_singleton] at member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj member
    simp [Expr.locationValue,regVal,gpr]
  · intro loc miss
    cases loc with
    | flag i => exact fl i
    | reg r' =>
      cases r' with
      | sp => exact sp
      | x j =>
        have ne : r ≠ j := by
          intro h; subst j; exact miss e (by simp)
        simp [Expr.locationValue,regVal,gpr,Vector.getElem_set,Fin.val_inj,ne]

theorem native_G (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (budget : Nat) (quiet : HookQuiet (budget+1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (view : Physical.BytePA) (regions : List Region) :
    ∃ fin, nativeTail real source (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched = .ok () fin ∧
      G.Holds view regions (.reg (.x (rk Rd)) (term Rd Rn imm6 Rm)) fetched fin ∧
      N1D226.SubShiftBorrow.ABI.Preserved source fin ∧ fin.events = fetched.events ∧
      fin.regs._PC = source.regs._PC + 4#64 := by
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,_,np,gic,dit⟩ :=
    N1D226.SubShiftBorrow.Tail.native_tail real source fetched enc0 Rd Rn imm6 Rm rd rn rm pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16 (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.SubShiftBorrow.expected (actionState (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16) Rd Rn imm6 Rm).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hp⟩ := shape (actionState (N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) sp 16) Rd Rn imm6 Rm rd rn rm ap.spe
  rw [←actualRegs] at hg hs hp
  have gA := ActionTransport.gpr (w := N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) (K := 16) post.frame
  have pA := ActionTransport.pstate (w := N1D226.SubShiftBorrow.Encoding.selected Rd Rn imm6 Rm) (K := 16) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val
      (Expr.eval (srcVal fetched) (term Rd Rn imm6 Rm)) (rk Rd).isLt := by
    rw [output.gpr,hg]
    simp only [term_eval,gA]
  have sp0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have ps := hp.trans pA
  have flags := flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
    (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))
  exact ⟨fin,tail,⟨output_one fetched fin (rk Rd) (term Rd Rn imm6 Rm) gpr sp0 flags,mem⟩,
    N1D226.SubShiftBorrow.ABI.of_nonProj np,ev,pc⟩

#print axioms shape
#print axioms output_one
#print axioms native_G
end N1D226.SubShiftBorrow.ExprValue
