-- ArmCertValueTail.Subsi64: SUBS xd, xn, #imm value tail, certiffi row
-- (x d, ⟨sbc3,[r n,#imm,#1]⟩), flags sbc3N/Z/C/V on [r n,#imm,#1]. Sail facts: projecting drive_spec
-- (Memory's generalize-~imm technique for the sf-dependent widths) + pure BitVec bridges.
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
import HeapV2StepCerts.RootTailV
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace ArmCertValue.Subsi64
open ArmCertValue.Flags

set_option maxHeartbeats 800000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s
open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots ArmCertValue.Flags in
set_option maxHeartbeats 800000 in
theorem key (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (imm12 : BitVec 12) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rd Rn imm12 = .ok
    (s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64) (GPRSummary.key Rd.toNat).isLt,
     s.regs.SP_EL0,
     BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64).msb,
     (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat = imm12.toNat then 1#1 else 0#1),
     (if imm12.toNat ≤ (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat then 1#1 else 0#1),
     (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64).toInt = (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toInt - imm12.toNat then 0#1 else 1#1)) u := by
  unfold native
  simp only [hRd, hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr]
  apply ok_congr
  simp only [ArmFull.Register.PSTATE_set]
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = xn
  simp only [Prod.mk.injEq, (ex4 _ _ _ _).1, (ex4 _ _ _ _).2.1, (ex4 _ _ _ _).2.2.1, (ex4 _ _ _ _).2.2.2, true_and]
  dsimp only [BitVec.length]
  generalize hk : (~~~Sail.BitVec.zeroExtend imm12 (Sail.Int.toNatChecked 64)) = nimm
  have hval : (nimm.toNat : Int) = 18446744073709551615 - (imm12.toNat : Int) := by
    subst hk
    have : imm12.toNat < 4096 := imm12.isLt
    show ((~~~(BitVec.setWidth 64 imm12)).toNat : Int) = _
    rw [BitVec.toNat_not, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    omega
  have hval2 : (nimm.toNat : Int) = 18446744073709551615 - (imm12.toNat : Int) := hval
  have hn2 : nimm.toNat < 18446744073709551616 := by omega
  have ha := xn.isLt
  have ha' : xn.toNat < 18446744073709551616 := ha
  have hb : imm12.toNat < 4096 := imm12.isLt
  simp [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, Sail.BitVec.zeroExtend, Sail.Int.toNatChecked, integer_subrange, get_slice_int, IsZero, xcast]
  simp only [Sail.Int.toNatChecked] at hval
  have hv : ∀ T : Int, T = (xn.toNat : Int) + nimm.toNat + 1 →
      BitVec.extractLsb' 0 64 (BitVec.ofInt 65 T) = xn - BitVec.setWidth 64 imm12 := by
    intro T hT; subst hT
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_sub, BitVec.toNat_setWidth]
    have hlt : ((xn.toNat : Int) + nimm.toNat + 1) % 36893488147419103232 = ((xn.toNat + nimm.toNat + 1 : Nat) : Int) := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; push_cast; rfl
    rw [hlt, Int.toNat_natCast]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_sub, BitVec.toNat_setWidth, Sail.Int.toNatChecked]
    omega
  · rw [hv _ (by have := ha; omega)]
    generalize xn - BitVec.setWidth 64 imm12 = r
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simp [BitVec.join1, BitVec.access, BitVec.msb_eq_getLsbD_last]
    rw [getElem!_pos r 63 (by omega)]
    generalize r[63] = b
    cases b <;> rfl
  · split <;> split <;> rename_i h1 h2 <;> (try rfl) <;> exfalso
    · have e := congrArg BitVec.toNat (beq_iff_eq.mp h1)
      simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_ofNat, Sail.Int.toNatChecked] at e
      omega
    · simp only [BEq.beq, decide_eq_true_eq] at h1
      apply h1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_ofNat, Sail.Int.toNatChecked]
      omega
  · split <;> split <;> rename_i h1 h2 <;> (try rfl) <;> exfalso <;> omega
  · have hni : @BitVec.toInt 64 nimm = -1 - (imm12.toNat : Int) := by
      subst hk
      show (~~~(BitVec.setWidth 64 imm12)).toInt = _
      rw [BitVec.toInt_eq_toNat_cond]
      simp only [BitVec.toNat_not, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show imm12.toNat < 2 ^ 64 by omega)]
      split <;> omega
    rw [hni]
    have hT : (0:Int) ≤ ((xn.toNat : Int) + (@BitVec.toNat 64 nimm) + 1) % 36893488147419103232 := Int.emod_nonneg _ (by decide)
    have hval3 : ((@BitVec.toNat 64 nimm : Nat) : Int) = 18446744073709551615 - (imm12.toNat : Int) := hval2
    rw [Int.max_eq_left hT]
    simp only [BitVec.toInt_eq_toNat_cond, Int.bmod_def]
    split <;> split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | (exfalso; omega)
open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
theorem results (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    let t := ArmBridge.CruxCore.resSt s ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s)
    (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) s = .ok () t ∧
    t.regs.gpr = s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64) (GPRSummary.key Rd.toNat).isLt ∧
    t.regs.PSTATE.N = BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64).msb ∧
    t.regs.PSTATE.Z = (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat = imm12.toNat then 1#1 else 0#1) ∧
    t.regs.PSTATE.C = (if imm12.toNat ≤ (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat then 1#1 else 0#1) ∧
    t.regs.PSTATE.V = (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64).toInt = (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toInt - imm12.toNat then 0#1 else 1#1) := by
  obtain ⟨u, hu⟩ := key s Rd Rn imm12 hRd hRn
  have hc := (complete s Rd Rn imm12 rd rn el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s _ hc
  exact ⟨h1, congrArg (fun p => p.1) h2, congrArg (fun p => p.2.2.1) h2, congrArg (fun p => p.2.2.2.1) h2,
    congrArg (fun p => p.2.2.2.2.1) h2, congrArg (fun p => p.2.2.2.2.2) h2⟩

section Bridge
variable (x : BitVec 64) (imm12 : BitVec 12)

theorem val : x - imm12.setWidth 64 = x + ~~~(imm12.setWidth 64) + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  have := imm12.isLt; have := x.isLt
  simp [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_setWidth]
  omega

theorem cflag : ((if imm12.toNat ≤ x.toNat then 1#1 else 0#1).setWidth 64) =
    b01 (decide (2 ^ 64 ≤ x.toNat + (~~~(imm12.setWidth 64)).toNat + (1#64).toNat)) := by
  have := imm12.isLt; have := x.isLt
  rw [Flags.b01_ite]; congr 1; apply decide_eq_decide.mpr
  simp [BitVec.toNat_not, BitVec.toNat_setWidth]; omega

theorem zflag : ((if x.toNat = imm12.toNat then 1#1 else 0#1).setWidth 64) =
    b01 (x + ~~~(imm12.setWidth 64) + 1#64 == 0#64) := by
  rw [Flags.b01_ite, ← val]
  congr 1
  have := imm12.isLt; have := x.isLt
  by_cases h : x.toNat = imm12.toNat
  · simp only [h, decide_true]; symm; simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_setWidth]; omega
  · simp only [h, decide_false]; symm; simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; apply h; have e2 := congrArg BitVec.toNat e
    simp [BitVec.toNat_sub, BitVec.toNat_setWidth] at e2; omega

theorem nflag : (BitVec.ofBool (x - imm12.setWidth 64).msb).setWidth 64 =
    b01 (x + ~~~(imm12.setWidth 64) + 1#64).msb := by
  rw [Flags.b01_ofBool, val]

theorem vflag : ((if (x - imm12.setWidth 64).toInt = x.toInt - imm12.toNat then 0#1 else 1#1).setWidth 64) =
    b01 (decide (x.toInt + (~~~(imm12.setWidth 64)).toInt + (1#64).toNat < -2 ^ 63 ∨
      2 ^ 63 ≤ x.toInt + (~~~(imm12.setWidth 64)).toInt + (1#64).toNat)) := by
  have hi := imm12.isLt
  have hni : (~~~(imm12.setWidth 64)).toInt = -1 - (imm12.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp only [BitVec.toNat_not, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show imm12.toNat < 2 ^ 64 by omega)]
    split <;> omega
  rw [hni]
  have hy : (imm12.setWidth 64).toInt = (imm12.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show imm12.toNat < 2 ^ 64 by omega)]
    split <;> omega
  have hs : (x - imm12.setWidth 64).toInt = (x.toInt - imm12.toNat).bmod (2 ^ 64) := by
    rw [BitVec.toInt_sub, hy]
  have hx1 := BitVec.le_toInt x
  have hx2 := BitVec.toInt_lt (x := x)
  simp at hx1 hx2
  rw [hs]
  have e1 : (1#64).toNat = 1 := rfl
  rw [e1]
  by_cases h : (x.toInt - (imm12.toNat : Int)).bmod (2 ^ 64) = x.toInt - imm12.toNat
  · rw [if_pos h]
    have hn : ¬ (x.toInt + (-1 - (imm12.toNat : Int)) + ((1 : Nat) : Int) < -2 ^ 63 ∨
        2 ^ 63 ≤ x.toInt + (-1 - (imm12.toNat : Int)) + ((1 : Nat) : Int)) := by
      rw [Int.bmod_def] at h; split at h <;> omega
    rw [decide_eq_false hn]; rfl
  · rw [if_neg h]
    have hp : (x.toInt + (-1 - (imm12.toNat : Int)) + ((1 : Nat) : Int) < -2 ^ 63 ∨
        2 ^ 63 ≤ x.toInt + (-1 - (imm12.toNat : Int)) + ((1 : Nat) : Int)) := by
      refine Classical.byContradiction fun hc => ?_
      apply h; rw [Int.bmod_def]; split <;> omega
    rw [decide_eq_true hp]; rfl
end Bridge

open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryBodySubsi64
open HeapV2StepCerts


open HeapV2StepCerts.RegBind (Reg regVal rk)
def args (Rn : BitVec 5) (imm12 : BitVec 12) : List Src := [.reg (.x (rk Rn)), .lit (imm12.setWidth 64), .lit 1#64]
def upd (Rd Rn : BitVec 5) (imm12 : BitVec 12) : List (Reg × Option VUpd) := [(.x (rk Rd), some ⟨.sbc3, args Rn imm12⟩)]
def fl (Rn : BitVec 5) (imm12 : BitVec 12) : VUpd × VUpd × VUpd × VUpd :=
  (⟨.sbc3N, args Rn imm12⟩, ⟨.sbc3Z, args Rn imm12⟩, ⟨.sbc3C, args Rn imm12⟩, ⟨.sbc3V, args Rn imm12⟩)

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn : BitVec 5) (imm12 : BitVec 12)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) 31 12 == 879088#20) = false) :
    ClassTailXAt real (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) NativeEntryBodyFlag.Subsi64.writes 21
      source (source.regs._PC + 4#64) (upd Rd Rn imm12) (some (fl Rn imm12)) := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, ha⟩ :=
    HeapV2StepCerts.RootV.Subsi64.native_tailV real source fetched enc0 Rd Rn imm12 rd rn noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) 21
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) sp 21 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) 21
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.Subsi64.Guard (actionState (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) sp 21) Rd Rn imm12 := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  have e2 : ArmBridge.CruxCore.resSt (actionState (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) sp 21) ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit) (actionState (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) sp 21)) = a := ha.symm
  have RS := results (actionState (NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) sp 21) Rd Rn imm12 classGuard.rd classGuard.rn classGuard.el classGuard.a64 classGuard.aa64 classGuard.btype classGuard.btn (by have := classGuard.rd; omega) (by have := classGuard.rn; omega)
  rw [e2] at RS
  have fG := RS.2.1
  have fN := RS.2.2.1
  have fZ := RS.2.2.2.1
  have fC := RS.2.2.2.2.1
  have fV := RS.2.2.2.2.2
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.Subsi64.selected Rd Rn imm12) (K := 21) post.frame
  simp only [gA] at fG fN fZ fC fV
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  apply vholds_set1_fl fetched fin (rk Rd) _ (fetched.regs.gpr[(GPRSummary.key Rn.toNat).val] - imm12.setWidth 64) _ _ _ _ (output.gpr.trans fG) sp0 (val _ _)
  · show (fin.regs.PSTATE.N).setWidth 64 = _
    rw [output.n, fN]; exact nflag _ _
  · show (fin.regs.PSTATE.Z).setWidth 64 = _
    rw [output.zf, fZ]; exact zflag _ _
  · show (fin.regs.PSTATE.C).setWidth 64 = _
    rw [output.c, fC]; exact cflag _ _
  · show (fin.regs.PSTATE.V).setWidth 64 = _
    rw [output.v, fV]; exact vflag _ _

#print axioms tailX
end ArmCertValue.Subsi64
