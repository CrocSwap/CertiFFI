-- ArmCertValueTail.Sbc64: SBC xd, xn, xzr value tail, certiffi row
-- (x d, ⟨sbc3,[r n,#0,F 2]⟩), fl none. Sail facts: a compact projecting drive_spec root of decode_sbc (no unfold of
-- whole-state effect_native, whose kernel check exceeds 12 GB); ~~~0 handled by BitVec.not_zero rewriting.
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
import HeapV2StepCerts.RootTailV
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace ArmCertValue.Sbc64
open ArmCertValue.Flags

set_option maxHeartbeats 4000000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 0#1 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s
theorem k2a (x : BitVec 64) (c : BitVec 1) : (x + ~~~0#64 + c.setWidth 64).toNat = (x.toNat + 18446744073709551615 + c.toNat) % 18446744073709551616 := by
  have := c.isLt
  rw [BitVec.not_zero, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_allOnes, BitVec.toNat_setWidth]
  omega
theorem k3 (x : BitVec 64) (c : BitVec 1) :
    (Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64) (integer_subrange
      ((BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0)).toNat + 18446744073709551615 + (c.toNat : Int)) 63 0)) 64).toNat
      = (x.toNat + 18446744073709551615 + c.toNat) % 18446744073709551616 := by
  have := c.isLt; have := x.isLt
  simp [Functions.integer_subrange, Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked,
    BitVec.extractLsb', BitVec.toNat_ofInt, Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.Int.toNatChecked]
  omega

theorem val (x : BitVec 64) (c : BitVec 1) :
    Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64) (integer_subrange
      ((BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0)).toNat + 18446744073709551615 + (c.toNat : Int)) 63 0)) 64
      = x + ~~~0#64 + c.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [k3 x c, k2a x c]

open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
set_option maxHeartbeats 4000000 in
theorem key (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rd Rn = .ok
      (s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt,
       s.regs.SP_EL0, s.regs.PSTATE.N, s.regs.PSTATE.Z, s.regs.PSTATE.C, s.regs.PSTATE.V) u := by
  unfold native
  simp only [hRd, hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr, ArmFull.Register.PSTATE_set]
  apply ok_congr
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = x
  generalize s.regs.PSTATE.C = c
  rw [val x c]
open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
theorem results (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    let t := ArmBridge.CruxCore.resSt s ((decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 0#1 1#1 1#1 : SailM Unit) s)
    (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 0#1 1#1 1#1 : SailM Unit) s = .ok () t ∧
    t.regs.gpr = s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt ∧
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
open ArmBridge.CruxGenGuarded.EntryBodySbc64
open HeapV2StepCerts


open HeapV2StepCerts.RegBind (Reg regVal rk)

def upd (Rd Rn : BitVec 5) : List (Reg × Option VUpd) :=
  [(.x (rk Rd), some ⟨.sbc3, [.reg (.x (rk Rn)), .lit 0#64, .flag 2]⟩)]

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) 31 12 == 879088#20) = false)
    (profile : NativeEntryBodyAdapters.Sbc64.Profile source) :
    ClassTailXAt real (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) NativeEntryBodyAdapters.Sbc64.writes 8
      source (source.regs._PC + 4#64) (upd Rd Rn) none := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, ha⟩ :=
    HeapV2StepCerts.RootV.Sbc64.native_tailV real source fetched enc0 Rd Rn rd rn profile noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) 8
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) sp 8 (budget + 1) post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.Sbc64.Guard (actionState (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) sp 8) Rd Rn := by
    exact NativeEntryBodyAdapters.Sbc64.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) 8 profile currentInput.controls currentPins (budget + 1) post.quiet rd rn
  have e2 : ArmBridge.CruxCore.resSt (actionState (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) sp 8) ((decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 0#1 1#1 1#1 : SailM Unit) (actionState (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) sp 8)) = a := ha.symm
  have RS := results (actionState (NativeEntryBodyDispatch.Sbc64.selected Rd Rn) sp 8) Rd Rn classGuard.rd classGuard.rn classGuard.el classGuard.a64 classGuard.aa64 classGuard.btype classGuard.btn (by have := classGuard.rd; omega) (by have := classGuard.rn; omega)
  rw [e2] at RS
  have fG := RS.2.1
  have fN := RS.2.2.1
  have fZ := RS.2.2.2.1
  have fC := RS.2.2.2.2.1
  have fV := RS.2.2.2.2.2
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.Sbc64.selected Rd Rn) (K := 8) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.Sbc64.selected Rd Rn) (K := 8) post.frame
  simp only [gA, pA] at fG fN fZ fC fV
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  apply vholds_set1 fetched fin (rk Rd) _ _ (output.gpr.trans fG) sp0 rfl
  exact flags_of (output.n.trans fN) (output.zf.trans fZ) (output.c.trans fC) (output.v.trans fV)

#print axioms tailX
end ArmCertValue.Sbc64
