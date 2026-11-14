-- ArmCertValueTail.Sbcs64: SBCS xd, xn, xzr value tail, certiffi row
-- (x d, ⟨sbc3,[r n,#0,F 2]⟩), flags (sbc3N, sbc3Z, sbc3C, sbc3V) on [r n, #0, F 2]. Sail facts: a projecting
-- drive_spec root of decode_sbcs with a generic Rm (operand ~~~X[Rm] symbolic), specialised to Rm = XZR in `key`.
import ArmCertValueTail.Flags
import HeapV2StepCerts.FlagRootV
import HeapV2StepCerts.RootTailVE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace ArmCertValue.Sbcs64
open ArmCertValue.Flags

set_option maxHeartbeats 4000000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd Rn Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s
theorem k2a (x : BitVec 64) (c : BitVec 1) : (x + ~~~0#64 + c.setWidth 64).toNat = (x.toNat + 18446744073709551615 + c.toNat) % 18446744073709551616 := by
  have := c.isLt
  rw [BitVec.not_zero, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_allOnes, BitVec.toNat_setWidth]
  omega
theorem k3 (x : BitVec 64) (c : BitVec 1) :
    (Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + 18446744073709551615 + (c.toNat : Int)) 63 0)) 64).toNat
      = (x.toNat + 18446744073709551615 + c.toNat) % 18446744073709551616 := by
  have := c.isLt; have := x.isLt
  simp [Functions.integer_subrange, Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked,
    BitVec.extractLsb', BitVec.toNat_ofInt, Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.Int.toNatChecked]
  omega
theorem val2 (x : BitVec 64) (c : BitVec 1) :
    Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + 18446744073709551615 + (c.toNat : Int)) 63 0)) 64
      = x + ~~~0#64 + c.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [k3 x c, k2a x c]

theorem iteTT {α : Sort _} (a b : α) : (if true = true then a else b) = a := rfl

theorem gval (x y : BitVec 64) (c : BitVec 1) :
    Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + ((18446744073709551615 - y.toNat : Nat) : Int) + (c.toNat : Int)) 63 0)) 64
      = x + ~~~y + c.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have := c.isLt; have := x.isLt; have := y.isLt
  simp [Functions.integer_subrange, Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked,
    BitVec.extractLsb', BitVec.toNat_ofInt, Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.Int.toNatChecked,
    BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_setWidth]
  omega

open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots HeapV2StepCerts.FlagRoots.TstF4 ArmCertValue.Flags in
set_option maxHeartbeats 4000000 in
theorem key_rm (s : ArmBridge.Draft.NativeState) (Rd Rn Rm : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31)
    (y : BitVec 64) (hY : (if (Rm.toNat : Int) = 31 then 0#64 else BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rm.toNat).val] (Int.toNatChecked 63) 0)) = y) :
    ∃ u, native s Rd Rn Rm = .ok
      (s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~y + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt,
       s.regs.SP_EL0, BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~y + s.regs.PSTATE.C.setWidth 64).msb, (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~y + s.regs.PSTATE.C.setWidth 64) = 0#64 then 1#1 else 0#1),
       (if 2 ^ 64 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~y).toNat + s.regs.PSTATE.C.toNat then 1#1 else 0#1),
       (if s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~y).toInt + s.regs.PSTATE.C.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~y).toInt + s.regs.PSTATE.C.toNat then 1#1 else 0#1)) u := by
  unfold native
  simp only [hRd, hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr, ArmFull.Register.PSTATE_set]
  simp only [hY, iteTT]
  apply ok_congr
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = x
  generalize s.regs.PSTATE.C = c
  have hx : (BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0)) = x := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.toNatChecked]
  have hR : (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + (~~~y).toNat + c.toNat) ((64 : Nat) - 1) 0)) = x + ~~~y + c.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [Functions.integer_subrange, BitVec.castWidth, Sail.get_slice_int, BitVec.extractLsb', BitVec.toNat_ofInt,
      BitVec.toNat_add, BitVec.toNat_setWidth, Sail.Int.toNatChecked, Int.toNatChecked, BitVec.toNat_ofNat]
    omega
  simp only [hx, Bool.false_eq_true, ite_false, BitVec.length]
  simp only [Prod.mk.injEq, hR, gval, (ex4 _ _ _ _).1, (ex4 _ _ _ _).2.1, (ex4 _ _ _ _).2.2.1, (ex4 _ _ _ _).2.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · have hxN : (BitVec.castWidth (n := Int.toNatChecked 63 + 1) (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0)) = x := hx
    have hYN : (if (Rm.toNat : Int) = 31 then 0#64 else BitVec.castWidth (n := Int.toNatChecked 63 + 1) (m := 64)
        (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rm.toNat).val] (Int.toNatChecked 63) 0)) = y := hY
    rw [hxN, hYN]
    have hRN : (BitVec.castWidth (n := Int.toNatChecked ((((64 : Nat) : Int) - 1) - 0 + 1)) (m := 64)
        (integer_subrange ((x.toNat : Int) + (~~~y).toNat + c.toNat) (((64 : Nat) : Int) - 1) 0)) = x + ~~~y + c.setWidth 64 := hR
    rw [hRN]
    exact nflag _
  · exact zflag _
  · exact cflag x (~~~y) c
  · exact vflag x (~~~y) c

open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
/-- SBCS Xd, Xn, XZR (heap-v2 rows): the projected root's values. -/
theorem key (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rd Rn 31#5 = .ok
      (s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt,
       s.regs.SP_EL0, BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64).msb, (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64) = 0#64 then 1#1 else 0#1),
       (if 2 ^ 64 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~0#64).toNat + s.regs.PSTATE.C.toNat then 1#1 else 0#1),
       (if s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~0#64).toInt + s.regs.PSTATE.C.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~0#64).toInt + s.regs.PSTATE.C.toNat then 1#1 else 0#1)) u :=
  key_rm s Rd Rn 31#5 hRd hRn 0#64 (if_pos (by decide))

open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
theorem results (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    let t := ArmBridge.CruxCore.resSt s ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s)
    (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s = .ok () t ∧
    t.regs.gpr = s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt ∧
    t.regs.PSTATE.N = BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64).msb ∧ t.regs.PSTATE.Z = (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64) = 0#64 then 1#1 else 0#1) ∧
    t.regs.PSTATE.C = (if 2 ^ 64 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~0#64).toNat + s.regs.PSTATE.C.toNat then 1#1 else 0#1) ∧ t.regs.PSTATE.V = (if s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~0#64).toInt + s.regs.PSTATE.C.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~0#64).toInt + s.regs.PSTATE.C.toNat then 1#1 else 0#1) := by
  obtain ⟨u, hu⟩ := key s Rd Rn hRd hRn
  have hc := (complete s Rd Rn 31#5 rd rn el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s _ hc
  exact ⟨h1, congrArg (fun p => p.1) h2, congrArg (fun p => p.2.2.1) h2, congrArg (fun p => p.2.2.2.1) h2,
    congrArg (fun p => p.2.2.2.2.1) h2, congrArg (fun p => p.2.2.2.2.2) h2⟩

open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryBodySbcs64
open HeapV2StepCerts



open HeapV2StepCerts.RegBind (Reg regVal rk)

def args (Rn : BitVec 5) : List Src := [.reg (.x (rk Rn)), .lit 0#64, .flag 2]
def upd (Rd Rn : BitVec 5) : List (Reg × Option VUpd) := [(.x (rk Rd), some ⟨.sbc3, args Rn⟩)]
def fl (Rn : BitVec 5) : VUpd × VUpd × VUpd × VUpd :=
  (⟨.sbc3N, args Rn⟩, ⟨.sbc3Z, args Rn⟩, ⟨.sbc3C, args Rn⟩, ⟨.sbc3V, args Rn⟩)

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) 31 12 == 879088#20) = false) :
    ClassTailXAt real (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) NativeEntryBodyFlag.Sbcs64.writes 9
      source (source.regs._PC + 4#64) (upd Rd Rn) (some (fl Rn)) := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, ha⟩ :=
    HeapV2StepCerts.FlagV.Sbcs64.native_tailV real source fetched enc0 Rd Rn rd rn noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) 9
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) sp 9 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) 9
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.Sbcs64.Guard (actionState (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) sp 9) Rd Rn := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  have RS := results (actionState (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) sp 9) Rd Rn classGuard.rd classGuard.rn classGuard.el classGuard.a64 classGuard.aa64 classGuard.btype classGuard.btn (by have := classGuard.rd; omega) (by have := classGuard.rn; omega)
  dsimp only at RS
  have e2 : ArmBridge.CruxCore.resSt (actionState (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) sp 9) ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) (actionState (NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) sp 9)) = a := ha.symm
  rw [e2] at RS
  have fG := RS.2.1
  have fN := RS.2.2.1
  have fZ := RS.2.2.2.1
  have fC := RS.2.2.2.2.1
  have fV := RS.2.2.2.2.2
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) (K := 9) post.frame
  have pA := ActionTransport.pstate (w := NativeEntryBodyDispatch.Sbcs64.selected Rd Rn) (K := 9) post.frame
  rw [gA, pA] at fG fN fZ fC fV
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  apply vholds_set1_fl fetched fin (rk Rd) _ _ _ _ _ _ (output.gpr.trans fG) sp0 rfl
  · show (fin.regs.PSTATE.N).setWidth 64 = _
    rw [output.n, fN, b01_ofBool]; rfl
  · show (fin.regs.PSTATE.Z).setWidth 64 = b01 (fetched.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + (fetched.regs.PSTATE.C.setWidth 64) == 0#64)
    rw [output.zf, fZ, b01_ite]; rfl
  · show (fin.regs.PSTATE.C).setWidth 64 = b01 (decide (2 ^ 64 ≤ fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~0#64).toNat + (fetched.regs.PSTATE.C.setWidth 64).toNat))
    rw [output.c, fC, b01_ite, toNat_c64]
  · show (fin.regs.PSTATE.V).setWidth 64 =
      b01 (decide (fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~0#64).toInt + (fetched.regs.PSTATE.C.setWidth 64).toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~0#64).toInt + (fetched.regs.PSTATE.C.setWidth 64).toNat))
    rw [output.v, fV, b01_ite, toNat_c64]

#print axioms tailX
end ArmCertValue.Sbcs64
