-- LRSbc.SbcsRegKey (, d192 Sbcs64Reg): SBCS Xd, Xn, Xm (register operand) Sail values, from the
-- generic-Rm projecting root of LRSbc.SbcsKey2 (key_rm at y := X[Rm], Rm ≠ 31).
import LRSbc.SbcsKey2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace LRSbc.SbcsRegKey
open LRSbc.SbcsKey2

theorem hY (s : ArmBridge.Draft.NativeState) (Rm : BitVec 5) (hRm : ¬ (Rm.toNat : Int) = 31) :
    (if (Rm.toNat : Int) = 31 then 0#64 else BitVec.castWidth (m := 64)
      (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rm.toNat).val] (Int.toNatChecked 63) 0)) =
      s.regs.gpr[(GPRSummary.key Rm.toNat).val] := by
  rw [if_neg hRm]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.toNatChecked]

theorem key (s : ArmBridge.Draft.NativeState) (Rd Rn Rm : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31)
    (hRn : ¬ (Rn.toNat : Int) = 31) (hRm : ¬ (Rm.toNat : Int) = 31) :
    ∃ u, native s Rd Rn Rm = .ok
      (s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val] + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt,
       s.regs.SP_EL0,
       BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val] + s.regs.PSTATE.C.setWidth 64).msb,
       (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val] + s.regs.PSTATE.C.setWidth 64) = 0#64 then 1#1 else 0#1),
       (if 2 ^ 64 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val]).toNat + s.regs.PSTATE.C.toNat then 1#1 else 0#1),
       (if s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val]).toInt + s.regs.PSTATE.C.toNat < -2 ^ 63 ∨
           2 ^ 63 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val]).toInt + s.regs.PSTATE.C.toNat then 1#1 else 0#1)) u :=
  key_rm s Rd Rn Rm hRd hRn _ (hY s Rm hRm)

open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
theorem results (s : ArmBridge.Draft.NativeState) (Rd Rn Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (rm : Rm.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true)
    (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) :
    let t := ArmBridge.CruxCore.resSt s ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 1#1 1#1 : SailM Unit) s)
    (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 1#1 1#1 : SailM Unit) s = .ok () t ∧
    t.regs.gpr = s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val] + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt ∧
    t.regs.SP_EL0 = s.regs.SP_EL0 ∧
    t.regs.PSTATE.N = BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val] + s.regs.PSTATE.C.setWidth 64).msb ∧
    t.regs.PSTATE.Z = (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val] + s.regs.PSTATE.C.setWidth 64) = 0#64 then 1#1 else 0#1) ∧
    t.regs.PSTATE.C = (if 2 ^ 64 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val]).toNat + s.regs.PSTATE.C.toNat then 1#1 else 0#1) ∧
    t.regs.PSTATE.V = (if s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val]).toInt + s.regs.PSTATE.C.toNat < -2 ^ 63 ∨
           2 ^ 63 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~s.regs.gpr[(GPRSummary.key Rm.toNat).val]).toInt + s.regs.PSTATE.C.toNat then 1#1 else 0#1) := by
  obtain ⟨u, hu⟩ := key s Rd Rn Rm (by omega) (by omega) (by omega)
  have hc := (complete s Rd Rn Rm rd rn el a64 aa64 btype btn).trans hu
  have h1 := ArmBridge.RootFrame.ok_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s u _ hc
  have h2 := ArmBridge.RootFrame.val_of_root _
    (fun u => (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) s _ hc
  exact ⟨h1, congrArg (fun p => p.1) h2, congrArg (fun p => p.2.1) h2, congrArg (fun p => p.2.2.1) h2,
    congrArg (fun p => p.2.2.2.1) h2, congrArg (fun p => p.2.2.2.2.1) h2, congrArg (fun p => p.2.2.2.2.2) h2⟩

#print axioms key
#print axioms results
end LRSbc.SbcsRegKey
