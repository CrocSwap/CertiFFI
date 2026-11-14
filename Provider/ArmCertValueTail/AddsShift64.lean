-- ArmCertValueTail.AddsShift64: ADCS xd, xn, xm value tail, certiffi table row
-- (x d, ⟨add3,[r n, r m, F 2]⟩), flags (add3N, add3Z, carry3, ovf3) on [r n, r m, F 2].
-- Sail facts: a drive_spec of the selected decoder projecting (gpr, SP, N, Z, C, V) (Memory's FlagRootsNZCV
-- pattern); the step prefix/tail are Core's generated RootV.AddsShift64 proofs with those facts carried out.
import ArmCertValueTail.Flags
import HeapV2StepCerts.RootTailVE
import HeapV2StepCerts.RootTailV
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace ArmCertValue.AddsShift64

theorem shl0i {w : Nat} (y : BitVec w) : y <<< (0 : Int) = y := by
  show y.shiftLeft 0 = y
  exact BitVec.shiftLeft_zero y
open ArmCertValue.Flags

set_option maxHeartbeats 800000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd Rn Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn 0#6 Rm 0#2 1#1 0#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s
open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots HeapV2StepCerts.FlagRoots.TstF4 in
set_option maxHeartbeats 800000 in
theorem key (s : ArmBridge.Draft.NativeState) (Rd Rn Rm : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) (hRm : ¬ (Rm.toNat : Int) = 31) :
    ∃ u, native s Rd Rn Rm = .ok
      (let x := s.regs.gpr[(GPRSummary.key Rn.toNat).val]; let y := s.regs.gpr[(GPRSummary.key Rm.toNat).val]
       let r := x + y + (0#1 : BitVec 1).setWidth 64
       (s.regs.gpr.set (GPRSummary.key Rd.toNat).val r (GPRSummary.key Rd.toNat).isLt, s.regs.SP_EL0,
        BitVec.ofBool r.msb, (if r = 0#64 then 1#1 else 0#1),
        (if 2 ^ 64 ≤ x.toNat + y.toNat + (0#1 : BitVec 1).toNat then 1#1 else 0#1),
        (if x.toInt + y.toInt + (0#1 : BitVec 1).toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt + y.toInt + (0#1 : BitVec 1).toNat then 1#1 else 0#1))) u := by
  unfold native
  simp only [hRd, hRn, hRm, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr, ArmFull.Register.PSTATE_set]
  apply ok_congr
  try simp only [shl0i]
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = x
  generalize s.regs.gpr[(GPRSummary.key Rm.toNat).val] = y
  have hx : (BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0)) = x := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.toNatChecked]
  have hy : (BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y (Int.toNatChecked 63) 0)) = y := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.toNatChecked]
  have hR : (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + y.toNat + (0#1 : BitVec 1).toNat) ((64 : Nat) - 1) 0)) = x + y + (0#1 : BitVec 1).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [Functions.integer_subrange, BitVec.castWidth, Sail.get_slice_int, BitVec.extractLsb', BitVec.toNat_ofInt,
      BitVec.toNat_add, BitVec.toNat_setWidth, Sail.Int.toNatChecked, Int.toNatChecked, BitVec.toNat_ofNat]
    omega
  simp only [hx, hy, Bool.false_eq_true, ite_false, if_false, BitVec.length]
  simp only [Prod.mk.injEq, hR, (ex4 _ _ _ _).1, (ex4 _ _ _ _).2.1, (ex4 _ _ _ _).2.2.1, (ex4 _ _ _ _).2.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · congr 1
    try (apply BitVec.eq_of_toNat_eq
         simp [Functions.integer_subrange, Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked,
           BitVec.extractLsb', BitVec.toNat_ofInt, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.toNat_add, BitVec.toNat_setWidth, shl0i]
         try omega)
  · trivial
  · try simp only [iteFF, Sail.BitVec.length]
    have hxN : (BitVec.castWidth (n := Int.toNatChecked 63 + 1) (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0)) = x := hx
    have hyN : (BitVec.castWidth (n := Int.toNatChecked 63 + 1) (m := 64) (Sail.BitVec.extractLsb y (Int.toNatChecked 63) 0)) = y := hy
    rw [hxN, hyN, shl0i y]
    have hRN : (BitVec.castWidth (n := Int.toNatChecked ((((64 : Nat) : Int) - 1) - 0 + 1)) (m := 64)
        (integer_subrange ((x.toNat : Int) + y.toNat + (0#1 : BitVec 1).toNat) (((64 : Nat) : Int) - 1) 0)) = x + y + (0#1 : BitVec 1).setWidth 64 := hR
    rw [hRN]
    exact nflag _
  · exact zflag _
  · exact cflag x y (0#1 : BitVec 1)
  · exact vflag x y (0#1 : BitVec 1)
open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
theorem results (s : ArmBridge.Draft.NativeState) (Rd Rn Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) (hRm : ¬ (Rm.toNat : Int) = 31) :
    let t := ArmBridge.CruxCore.resSt s ((decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn 0#6 Rm 0#2 1#1 0#1 1#1 : SailM Unit) s)
    (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn 0#6 Rm 0#2 1#1 0#1 1#1 : SailM Unit) s = .ok () t ∧
    t.regs.gpr = s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + s.regs.gpr[(GPRSummary.key Rm.toNat).val] + (0#1 : BitVec 1).setWidth 64) (GPRSummary.key Rd.toNat).isLt ∧
    t.regs.PSTATE.N = BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + s.regs.gpr[(GPRSummary.key Rm.toNat).val] + (0#1 : BitVec 1).setWidth 64).msb ∧ t.regs.PSTATE.Z = (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + s.regs.gpr[(GPRSummary.key Rm.toNat).val] + (0#1 : BitVec 1).setWidth 64) = 0#64 then 1#1 else 0#1) ∧
    t.regs.PSTATE.C = (if 2 ^ 64 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + s.regs.gpr[(GPRSummary.key Rm.toNat).val].toNat + (0#1 : BitVec 1).toNat then 1#1 else 0#1) ∧
    t.regs.PSTATE.V = (if s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + s.regs.gpr[(GPRSummary.key Rm.toNat).val].toInt + (0#1 : BitVec 1).toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + s.regs.gpr[(GPRSummary.key Rm.toNat).val].toInt + (0#1 : BitVec 1).toNat then 1#1 else 0#1) := by
  obtain ⟨u, hu⟩ := key s Rd Rn Rm hRd hRn hRm
  have hc := (complete s Rd Rn Rm rd rn rm el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s _ hc
  exact ⟨h1, congrArg (fun p => p.1) h2, congrArg (fun p => p.2.2.1) h2, congrArg (fun p => p.2.2.2.1) h2,
    congrArg (fun p => p.2.2.2.2.1) h2, congrArg (fun p => p.2.2.2.2.2) h2⟩

open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryBodyAddsShift64
open HeapV2StepCerts


open HeapV2StepCerts.RegBind (Reg regVal rk)
def args (Rn Rm : BitVec 5) : List Src := [.reg (.x (rk Rn)), .reg (.x (rk Rm)), .lit 0#64]
def upd (Rd Rn Rm : BitVec 5) : List (Reg × Option VUpd) := [(.x (rk Rd), some ⟨.add3, args Rn Rm⟩)]
def fl (Rn Rm : BitVec 5) : VUpd × VUpd × VUpd × VUpd :=
  (⟨.add3N, args Rn Rm⟩, ⟨.add3Z, args Rn Rm⟩, ⟨.carry3, args Rn Rm⟩, ⟨.ovf3, args Rn Rm⟩)

theorem tailX (real : Type) [Sail.SailReal real] (source : NativeState) (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (h6 : imm6 = 0#6)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn imm6 Rm) 31 12 == 879088#20) = false) :
    ClassTailXAt real (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn imm6 Rm) NativeEntryBodyFlag.AddsShift64.writes 15
      source (source.regs._PC + 4#64) (upd Rd Rn Rm) (some (fl Rn Rm)) := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, frame, q, p, sys, _, output, mem, ev, gic, _, pc, np, v, hg, hs, ha⟩ :=
    HeapV2StepCerts.RootV.AddsShift64.native_tailV real source fetched enc0 Rd Rn imm6 Rm rd rn rm noEret pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn 0#6 Rm) 15
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn 0#6 Rm) sp 15 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn 0#6 Rm) 15
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.AddsShift64.Guard (actionState (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn 0#6 Rm) sp 15) Rd Rn 0#6 Rm := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  have e2 : ArmBridge.CruxCore.resSt (actionState (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn 0#6 Rm) sp 15) ((decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn 0#6 Rm 0#2 1#1 0#1 1#1 : SailM Unit) (actionState (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn 0#6 Rm) sp 15)) = a := by rw [← h6]; exact ha.symm
  have RS := results (actionState (NativeEntryBodyDispatch.AddsShift64.selected Rd Rn 0#6 Rm) sp 15) Rd Rn Rm classGuard.rd classGuard.rn classGuard.rm classGuard.el classGuard.a64 classGuard.aa64 classGuard.btype classGuard.btn (by have := classGuard.rd; omega) (by have := classGuard.rn; omega) (by have := classGuard.rm; omega)
  rw [e2] at RS
  have fG := RS.2.1
  have fN := RS.2.2.1
  have fZ := RS.2.2.2.1
  have fC := RS.2.2.2.2.1
  have fV := RS.2.2.2.2.2
  try rw [← h6] at fG
  try rw [← h6] at fN
  try rw [← h6] at fZ
  try rw [← h6] at fC
  try rw [← h6] at fV
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ev, ValueTailE.z_tail quiet hook frame rfl np, ?_⟩
  have gA := ActionTransport.gpr (w := NativeEntryBodyDispatch.AddsShift64.selected Rd Rn imm6 Rm) (K := 15) post.frame
  simp only [gA] at fG fN fZ fC fV
  have sp0 : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := output.sp.trans (hs.trans (ActionTransport.sp0 post.frame))
  apply vholds_set1_fl fetched fin (rk Rd) _ _ _ _ _ _ (output.gpr.trans fG) sp0 rfl
  · show (fin.regs.PSTATE.N).setWidth 64 = _
    rw [output.n, fN, b01_ofBool]; rfl
  · show (fin.regs.PSTATE.Z).setWidth 64 = b01 (fetched.regs.gpr[(GPRSummary.key Rn.toNat).val] + fetched.regs.gpr[(GPRSummary.key Rm.toNat).val] + ((0#1 : BitVec 1).setWidth 64) == 0#64)
    rw [output.zf, fZ, b01_ite]; rfl
  · show (fin.regs.PSTATE.C).setWidth 64 = b01 (decide (2 ^ 64 ≤ fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + fetched.regs.gpr[(GPRSummary.key Rm.toNat).val].toNat + ((0#1 : BitVec 1).setWidth 64).toNat))
    rw [output.c, fC, b01_ite, toNat_c64]
  · show (fin.regs.PSTATE.V).setWidth 64 =
      b01 (decide (fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + fetched.regs.gpr[(GPRSummary.key Rm.toNat).val].toInt + ((0#1 : BitVec 1).setWidth 64).toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ fetched.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + fetched.regs.gpr[(GPRSummary.key Rm.toNat).val].toInt + ((0#1 : BitVec 1).setWidth 64).toNat))
    rw [output.v, fV, b01_ite, toNat_c64]

#print axioms tailX
end ArmCertValue.AddsShift64

