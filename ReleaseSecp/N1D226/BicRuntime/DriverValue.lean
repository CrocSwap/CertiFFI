import N1D226.BicRuntime.ExprValue
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.BicRuntime.DriverValue
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmCertValue HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

def selected (Rd Rn Rm : BitVec 5) : BitVec 32 := N1D226.BicRuntime.Encoding.selected Rd Rn 0#6 Rm

theorem selected_request : selected 10#5 1#5 0#5 = 2317353002#32 := by decide

def upd (source : NativeState) (Rd Rn Rm : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd),some ⟨.and,[.reg (.x (rk Rn)),.lit (~~~source.regs.gpr[(rk Rm).val])]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) :
    ClassTailXAt real (selected Rd Rn Rm) {} 50
      source (source.regs._PC + 4#64) (upd source Rd Rn Rm) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp,a,fin,hook,_,tail,projection,frame,q,p,sys,_,output,mem,ev,pc,np,_,gic,_⟩ :=
    N1D226.BicRuntime.Tail.native_tail real source fetched enc0 Rd Rn 0#6 Rm rd rn rm pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget+1) quiet hook
  have ap := metadata_pins (N1D226.BicRuntime.Encoding.selected Rd Rn 0#6 Rm) sp 50 (e20_pins fetched sp pins post.frame)
  have actualRegs : a.regs = (N1D226.BicRuntime.expected (actionState (N1D226.BicRuntime.Encoding.selected Rd Rn 0#6 Rm) sp 50) Rd Rn 0#6 Rm).1 :=
    congrArg Prod.fst projection
  obtain ⟨hg,hs,hp⟩ := N1D226.BicRuntime.ExprValue.shape (actionState (N1D226.BicRuntime.Encoding.selected Rd Rn 0#6 Rm) sp 50) Rd Rn 0#6 Rm rd rn rm ap.spe
  rw [←actualRegs] at hg hs hp
  have gA := ActionTransport.gpr (w := N1D226.BicRuntime.Encoding.selected Rd Rn 0#6 Rm) (K := 50) post.frame
  have pA := ActionTransport.pstate (w := N1D226.BicRuntime.Encoding.selected Rd Rn 0#6 Rm) (K := 50) post.frame
  have gpr : fin.regs.gpr = fetched.regs.gpr.set (rk Rd).val
      (fetched.regs.gpr[(rk Rn).val] &&& (~~~fetched.regs.gpr[(rk Rm).val])) (rk Rd).isLt := by
    rw [output.gpr,hg]
    have zero : (0#6).toNat = 0 := rfl
    simp only [N1D226.BicRuntime.ExprValue.term_eval,gA,zero,BitVec.shiftLeft_zero]
    rfl
  have sp0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  have ps := hp.trans pA
  refine ⟨sp,a,fin,hook,tail,frame,q,p,sys,mem,gic,pc,np,ev,
    ValueTailE.z_tail quiet hook frame rfl np,?_⟩
  refine vholds_set1 fetched fin (rk Rd) _ _ gpr sp0 ?_ ?_
  · change fetched.regs.gpr[(rk Rn).val] &&& (~~~fetched.regs.gpr[(rk Rm).val]) = _
    rw [input.gpr]; rfl
  · exact flags_of (output.n.trans (congrArg ProcState.N ps)) (output.zf.trans (congrArg ProcState.Z ps))
      (output.c.trans (congrArg ProcState.C ps)) (output.v.trans (congrArg ProcState.V ps))

theorem native_abi (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd Rn Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (budget : Nat) (quiet : HookQuiet (budget+1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source (selected Rd Rn Rm) enc0 fetched = .ok () fin ∧
      N1D226.BicRuntime.ABI.Preserved source fin ∧ fin.mem = fetched.mem ∧ fin.events = fetched.events ∧
      fin.regs._PC = source.regs._PC + 4#64 :=
  N1D226.BicRuntime.ABI.native_abi real source fetched enc0 Rd Rn 0#6 Rm rd rn rm pins input guard budget quiet it ss

#print axioms selected_request
#print axioms tailX
#print axioms native_abi

/-- State-independent instruction-local term, with no artificial SSA instruction. -/
def term (Rn Rm : BitVec 5) : Expr.Term :=
  .binary .and (.source (.reg (.x (rk Rn)))) (.unary .not (.source (.reg (.x (rk Rm)))))

def step (Rd Rn Rm : BitVec 5) : G.Step := .reg (.x (rk Rd)) (term Rn Rm)

theorem holds_of_native (bytePA : Physical.BytePA) (regions : List Region)
    (x y : NativeState) (Rd Rn Rm : BitVec 5)
    (hv : VHolds (upd x Rd Rn Rm) none x y) (hm : y.mem = x.mem) :
    G.Holds bytePA regions (step Rd Rn Rm) x y := by
  constructor
  · constructor
    · intro loc termVal member
      simp only [step,G.outputs,List.mem_singleton] at member
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj member
      have value := hv.1 (.x (rk Rd))
      simp only [upd,List.find?,decide_true,Option.map_some] at value
      exact value
    · intro loc untouched
      cases loc with
      | flag i => exact hv.2 i
      | reg reg =>
        have other : reg ≠ .x (rk Rd) := by
          intro equal; subst reg
          exact untouched (term Rn Rm) (by simp [step,G.outputs])
        have h := hv.1 reg
        simpa [upd,other,Ne.symm other,Expr.locationValue] using h
  · exact hm

#print axioms holds_of_native

theorem selected_word_8a28000a : selected 10#5 0#5 8#5 =
    2317877258#32 := by decide
#print axioms selected_word_8a28000a

theorem selected_word_8a2b010c : selected 12#5 8#5 11#5 =
    2318074124#32 := by decide
#print axioms selected_word_8a2b010c
end N1D226.BicRuntime.DriverValue
