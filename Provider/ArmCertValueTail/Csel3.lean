-- ArmCertValueTail.Csel3: CSEL xd, xn, xzr, CC value tail, certiffi table row
-- (x d, ⟨cselc cond, [F 0, F 1, F 2, F 3, r n, #0]⟩), fl none (NZCV unchanged).
import ArmCertValueTail.Flags
import HeapV2StepCerts.FlagRootVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace ArmCertValue.Csel3
open ArmCertValue.Flags

set_option maxHeartbeats 800000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s
open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots HeapV2StepCerts.FlagRoots.TstF4 in
set_option maxHeartbeats 800000 in
theorem key (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rd Rn = .ok (s.regs.gpr.set (GPRSummary.key Rd.toNat).val
        (if s.regs.PSTATE.C = 1#1 then 0#64 else s.regs.gpr[(GPRSummary.key Rn.toNat).val]) (GPRSummary.key Rd.toNat).isLt,
      s.regs.SP_EL0, s.regs.PSTATE.N, s.regs.PSTATE.Z, s.regs.PSTATE.C, s.regs.PSTATE.V) u := by
  unfold native
  simp only [hRd, hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr, ArmFull.Register.PSTATE_set]
  apply ok_congr
  by_cases hc : s.regs.PSTATE.C = 1#1 <;> simp only [hc, ite_true, ite_false, ↓reduceIte] <;> (try split) <;> (try split)
  all_goals simp only [Prod.mk.injEq]
  all_goals and_intros
  all_goals first
    | trivial
    | rfl
    | (show s.regs.gpr.set (GPRSummary.key Rd.toNat).val _ (GPRSummary.key Rd.toNat).isLt = _
       congr 1
       apply BitVec.eq_of_toNat_eq
       simp [Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.toNatChecked])
open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
theorem results (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    let t := ArmBridge.CruxCore.resSt s ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s)
    (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s = .ok () t ∧
    t.regs.gpr = s.regs.gpr.set (GPRSummary.key Rd.toNat).val (if s.regs.PSTATE.C = 1#1 then 0#64 else s.regs.gpr[(GPRSummary.key Rn.toNat).val]) (GPRSummary.key Rd.toNat).isLt ∧
    t.regs.PSTATE.N = s.regs.PSTATE.N ∧ t.regs.PSTATE.Z = s.regs.PSTATE.Z ∧
    t.regs.PSTATE.C = s.regs.PSTATE.C ∧ t.regs.PSTATE.V = s.regs.PSTATE.V := by
  obtain ⟨u, hu⟩ := key s Rd Rn hRd hRn
  have hc := (complete s Rd Rn rd rn el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s _ hc
  exact ⟨h1, congrArg (fun p => p.1) h2, congrArg (fun p => p.2.2.1) h2, congrArg (fun p => p.2.2.2.1) h2,
    congrArg (fun p => p.2.2.2.2.1) h2, congrArg (fun p => p.2.2.2.2.2) h2⟩

open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryBodyCsel3
open HeapV2StepCerts


open HeapV2StepCerts.RegBind (Reg regVal rk)

def upd (Rd Rn : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd), some ⟨.cselc 3#4, [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x (rk Rn)), .lit 0#64]⟩)]

/-- Sail's CSEL cond 3 (CC) branch = Core's cselc 3 over the NZCV words. -/
theorem cc_eq (n z v x : BitVec 64) (c : BitVec 1) :
    (if c = 1#1 then 0#64 else x) = (if condHolds 3#4 n z (c.setWidth 64) v then x else 0#64) := by
  rcases Flags.bv1 c with rfl | rfl <;> rfl

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Csel3.selected Rd Rn) 31 12 == 879088#20) = false) :
    ClassTailXAt real (NativeEntryBodyDispatch.Csel3.selected Rd Rn) NativeEntryBodyFlag.Csel3.writes 187
      source (source.regs._PC + 4#64) (upd Rd Rn) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, ha⟩ :=
    HeapV2StepCerts.FlagV.Csel3.native_tailV real source fetched enc0 Rd Rn rd rn noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Csel3.selected Rd Rn) 187
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Csel3.selected Rd Rn) sp 187 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Csel3.selected Rd Rn) 187
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.Csel3.Guard (actionState (NativeEntryBodyDispatch.Csel3.selected Rd Rn) sp 187) Rd Rn := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  have e2 : ArmBridge.CruxCore.resSt (actionState (NativeEntryBodyDispatch.Csel3.selected Rd Rn) sp 187) ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) (actionState (NativeEntryBodyDispatch.Csel3.selected Rd Rn) sp 187)) = a := ha.symm
  have RS := results (actionState (NativeEntryBodyDispatch.Csel3.selected Rd Rn) sp 187) Rd Rn classGuard.rd classGuard.rn classGuard.el classGuard.a64 classGuard.aa64 classGuard.btype classGuard.btn (by have := classGuard.rd; omega) (by have := classGuard.rn; omega)
  rw [e2] at RS
  have fG := RS.2.1
  have fN := RS.2.2.1
  have fZ := RS.2.2.2.1
  have fC := RS.2.2.2.2.1
  have fV := RS.2.2.2.2.2
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.Csel3.selected Rd Rn) (K := 187) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.Csel3.selected Rd Rn) (K := 187) post.frame
  simp only [gA, pA] at fG fN fZ fC fV
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  apply vholds_set1 fetched fin (rk Rd) _ _ (output.gpr.trans fG) sp0
  · exact cc_eq _ _ _ fetched.regs.gpr[(GPRSummary.key Rn.toNat).val] fetched.regs.PSTATE.C
  · exact flags_of (output.n.trans fN) (output.zf.trans fZ) (output.c.trans fC) (output.v.trans fV)

#print axioms tailX
end ArmCertValue.Csel3
