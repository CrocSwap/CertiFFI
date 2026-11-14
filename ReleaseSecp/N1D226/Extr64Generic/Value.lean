import N1D226.Extr64Generic.ABI
import CompiledLean.CmpArithmeticV1
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.Extr64Generic.Value
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

theorem extract_cast (x : BitVec 128) (n len : Nat) (h : len = 64) :
    Sail.BitVec.castWidth (m := 64) (BitVec.extractLsb' n len x) =
      BitVec.extractLsb' n 64 x := by
  subst len
  rfl

theorem sail_window (x : BitVec 128) (n : Nat) :
    Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x (n + 63) n) =
      BitVec.extractLsb' n 64 x := by
  exact extract_cast x n (n + 63 - n + 1) (by omega)

theorem sail_window_at (x : BitVec 128) (n high : Nat) (h : high = n + 63) :
    Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x high n) =
      BitVec.extractLsb' n 64 x := by
  subst high
  exact sail_window x n

theorem extract_shift (x y : BitVec 64) (n : Nat) (hn : n < 64) :
    BitVec.extractLsb' n 64 (x ++ y) = (x <<< (64 - n)) ||| (y >>> n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_append,
    BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight]
  by_cases h : n + i < 64
  · have hleft : i < 64 - n := by omega
    simp [hi,h,hleft]
  · have hleft : ¬ i < 64 - n := by omega
    have he : i - (64 - n) = n + i - 64 := by omega
    simp [hi,h,hleft,he,BitVec.getLsbD_of_ge y (n + i) (by omega)]

def value (s : NativeState) (Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5) : BitVec 64 :=
  BitVec.extractLsb' imms.toNat 64 (s.regs.gpr[(rk Rn).val] ++ s.regs.gpr[(rk Rm).val])

theorem shape (s : NativeState) (Rd Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (spe : s.regs.bank_Bool .SPESampleInFlight = false) :
    (N1D226.Extr64Generic.expected s Rd Rn imms Rm).1.gpr =
      s.regs.gpr.set (rk Rd).val (value s Rn imms Rm) (rk Rd).isLt ∧
    (N1D226.Extr64Generic.expected s Rd Rn imms Rm).1.SP_EL0 = s.regs.SP_EL0 ∧
    (N1D226.Extr64Generic.expected s Rd Rn imms Rm).1.PSTATE = s.regs.PSTATE := by
  have hd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hn : ¬ (Rn.toNat : Int) = 31 := by omega
  have hm : ¬ (Rm.toNat : Int) = 31 := by omega
  have hi := imms.isLt
  have hpos : (1 : Int) ≤ (imms.toNat : Int) + 64 := by omega
  have hpos' : (0 : Int) ≤ (imms.toNat : Int) + 64 - 1 := by omega
  have hnat : ((imms.toNat : Int) + 64).toNat = imms.toNat + 64 := by omega
  have hnat' : ((imms.toNat : Int) + 64 - 1).toNat = imms.toNat + 63 := by omega
  have hwidth : imms.toNat + 64 - 1 - imms.toNat = 63 := by omega
  unfold N1D226.Extr64Generic.expected N1D226.Extr64Generic.effect_native
  simp only [hd,hn,hm,spe,ite_true,ite_false,dite_eq_ite,ite_self,ArmFull.Register.PSTATE_set]
  and_intros
  all_goals simp [value,extract64,hpos,hpos',hnat,hnat',hwidth,
    CompiledLean.CmpArithmetic.V1.full_extract,Sail.BitVec.zeroExtend,
    BitVec.zeroExtend,Int.toNatChecked,Sail.Int.toNatChecked]
  all_goals first | rfl | skip
  apply congrArg (fun v : BitVec 64 => s.regs.gpr.set (rk Rd).val v (rk Rd).isLt)
  apply sail_window_at
  split <;> omega

def upd (source : NativeState) (Rd Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5) :
    List (Reg × Option VUpd) :=
  [(.x (rk Rd),some ⟨.orr,[.lit (source.regs.gpr[(rk Rn).val] <<< (64 - imms.toNat)),
    .lit (source.regs.gpr[(rk Rm).val] >>> imms.toNat)]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState)
    (Rd Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    ClassTailXAt real (N1D226.Extr64Generic.Encoding.selected Rd Rn imms Rm) {} 206
      source (source.regs._PC+4#64) (upd source Rd Rn imms Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,np,_,gic,_⟩ :=
    N1D226.Extr64Generic.Tail.native_tail real source fetched enc0 Rd Rn imms Rm rd rn rm pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.Extr64Generic.Encoding.selected Rd Rn imms Rm) sp 206 (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.Extr64Generic.expected
      (actionState (N1D226.Extr64Generic.Encoding.selected Rd Rn imms Rm) sp 206) Rd Rn imms Rm).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hp⟩ := shape (actionState (N1D226.Extr64Generic.Encoding.selected Rd Rn imms Rm) sp 206)
    Rd Rn imms Rm rd rn rm ap.spe
  rw [←actualRegs] at hg hs hp
  have gA := ActionTransport.gpr (w := N1D226.Extr64Generic.Encoding.selected Rd Rn imms Rm) (K := 206) post.frame
  have pA := ActionTransport.pstate (w := N1D226.Extr64Generic.Encoding.selected Rd Rn imms Rm) (K := 206) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val (value fetched Rn imms Rm) (rk Rd).isLt := by
    rw [output.gpr,hg]
    simp only [value,gA]
  have sp0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have ps := hp.trans pA
  refine ⟨sp,a,fin,hook,tail,frame,q,p,sys,mem,gic,pc,np,ev,
    ValueTailE.z_tail quiet hook frame rfl np,?_⟩
  refine vholds_set1 fetched fin (rk Rd) _ _ gpr sp0 ?_ ?_
  · change value fetched Rn imms Rm =
      (source.regs.gpr[(rk Rn).val] <<< (64 - imms.toNat)) |||
        (source.regs.gpr[(rk Rm).val] >>> imms.toNat)
    simp only [value,input.gpr]
    exact extract_shift _ _ _ imms.isLt
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

#print axioms extract_shift
#print axioms shape
#print axioms tailX
end N1D226.Extr64Generic.Value
