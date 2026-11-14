import N1D226.Umaddl64Generic.ABI
import N1D226.BicRuntime.ExprValue
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.Umaddl64Generic.ExprValue
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmCertValue HeapV2StepCerts
open HeapV2StepCerts.RegBind (rk)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] Sail.Int.toNatChecked

def term (Rn Rm : BitVec 5) : Expr.Term :=
  .binary .mul
    (.binary .and (.source (.reg (.x (rk Rn)))) (.literal 0xffffffff#64))
    (.binary .and (.source (.reg (.x (rk Rm)))) (.literal 0xffffffff#64))

theorem term_eval (s : NativeState) (Rn Rm : BitVec 5) :
    Expr.eval (srcVal s) (term Rn Rm) =
      (s.regs.gpr[(rk Rn).val] &&& 0xffffffff#64) *
      (s.regs.gpr[(rk Rm).val] &&& 0xffffffff#64) := rfl

theorem low32 (x : BitVec 64) :
    x &&& 0xffffffff#64 = (x.setWidth 32).setWidth 64 := by
  rw [BitVec.setWidth_eq_append (show 32 ≤ 64 by decide)]
  exact BitVec.and_setWidth_allOnes 32 32 x

theorem shape (s : NativeState) (Rd Rn Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (spe : s.regs.bank_Bool .SPESampleInFlight = false) :
    (N1D226.Umaddl64Generic.expected s Rd Rn Rm).1.gpr =
      s.regs.gpr.set (rk Rd).val (Expr.eval (srcVal s) (term Rn Rm)) (rk Rd).isLt ∧
    (N1D226.Umaddl64Generic.expected s Rd Rn Rm).1.SP_EL0 = s.regs.SP_EL0 ∧
    (N1D226.Umaddl64Generic.expected s Rd Rn Rm).1.PSTATE = s.regs.PSTATE := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hRn : ¬ (Rn.toNat : Int) = 31 := by omega
  have hRm : ¬ (Rm.toNat : Int) = 31 := by omega
  unfold N1D226.Umaddl64Generic.expected N1D226.Umaddl64Generic.effect_native
  simp only [hRd,hRn,hRm,spe,ite_true,ite_false,dite_eq_ite,ite_self]
  refine ⟨?_,by trivial,by trivial⟩
  rw [term_eval,low32,low32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Functions.integer_subrange,BitVec.castWidth,Sail.get_slice_int,
    BitVec.extractLsb',BitVec.toNat_ofInt,BitVec.toNat_mul,BitVec.toNat_setWidth,
    Sail.Int.toNatChecked,Int.toNatChecked,BitVec.toNat_ofNat,
    Sail.BitVec.zeroExtend,Sail.BitVec.extractLsb,BitVec.extractLsb]
  simp only [rk,←Int.natCast_emod,←Int.natCast_mul,Int.toNat_natCast]
  let left := s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat % 4294967296
  let right := s.regs.gpr[(GPRSummary.key Rm.toNat).val].toNat % 4294967296
  change ((left * right) % 36893488147419103232) % 18446744073709551616 =
    (left * right) % 18446744073709551616
  omega

theorem native_G (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (Rd Rn Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (budget : Nat) (quiet : HookQuiet (budget+1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (view : Physical.BytePA) (regions : List Region) :
    ∃ fin, nativeTail real source (N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm) enc0 fetched = .ok () fin ∧
      G.Holds view regions (.reg (.x (rk Rd)) (term Rn Rm)) fetched fin ∧
      N1D226.Umaddl64Generic.ABI.Preserved source fin ∧ fin.events = fetched.events ∧
      fin.regs._PC = source.regs._PC + 4#64 := by
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,_,np,gic,dit⟩ :=
    N1D226.Umaddl64Generic.Tail.native_tail real source fetched enc0 Rd Rn Rm rd rn rm pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm) sp 830 (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.Umaddl64Generic.expected (actionState (N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm) sp 830) Rd Rn Rm).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hp⟩ := shape (actionState (N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm) sp 830) Rd Rn Rm rd rn rm ap.spe
  rw [←actualRegs] at hg hs hp
  have gA := ActionTransport.gpr (w := N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm) (K := 830) post.frame
  have pA := ActionTransport.pstate (w := N1D226.Umaddl64Generic.Encoding.selected Rd Rn Rm) (K := 830) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val
      (Expr.eval (srcVal fetched) (term Rn Rm)) (rk Rd).isLt := by
    rw [output.gpr,hg]
    simp only [term_eval,gA]
  have sp0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have ps := hp.trans pA
  have flags := flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
    (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))
  exact ⟨fin,tail,⟨N1D226.BicRuntime.ExprValue.output_one fetched fin (rk Rd) (term Rn Rm) gpr sp0 flags,mem⟩,
    N1D226.Umaddl64Generic.ABI.of_nonProj np,ev,pc⟩

#print axioms low32
#print axioms shape
#print axioms native_G
end N1D226.Umaddl64Generic.ExprValue
