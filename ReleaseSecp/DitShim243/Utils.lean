import DefaultHeapShimEffects
import DitShim243.StateAt
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.Boundary RtDit ArmBridge.CruxCore ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
namespace DitShim243.Utils

theorem classE_toV {real : Type} [Sail.SailReal real] {w : BitVec 32} {writes : NativeEntry.Effects.Writes}
    {K : Int} {source : NativeState} {next : BitVec 64} {us : List (RegBind.Reg × RegBind.Upd)}
    (h : RegValE.ClassTailVAt real w writes K source next us) : RegVal.ClassTailVAt real w writes K source next us := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, run, frame, q, fp, sys, mem, gic, pc, np, _, _, holds⟩ :=
    h fetched enc0 budget pins input guard quiet it ss
  exact ⟨sp, a, fin, hook, run, frame, q, fp, sys, mem, gic, pc, np, holds⟩

theorem ev_succ {real : Type} [Sail.SailReal real] {e : NativeState} {j : Nat} {P : NativeState → Prop}
    (h : ∃ fin, modelStep real (stateAt real e j) = .ok () fin ∧ P fin) : P (stateAt real e (j + 1)) := by
  obtain ⟨fin, r, hp⟩ := h
  rw [stateAt_succ_of r]; exact hp
theorem ldpHi_stpData (s : NativeState) :
    ArmCertMem.LdpEval.ldpHi (ArmCertMem.StpEval.stpData s 9#5 30#5) = s.regs.gpr[30] := by
  unfold ArmCertMem.StpEval.stpData
  exact RtSaved.ldpHi_append _ _

private theorem ldpLo_append (hi lo : BitVec 64) :
    ArmCertMem.LdpEval.ldpLo (BitVec.cast (by decide : 64 + 64 = 128) (BitVec.append hi lo)) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [ArmCertMem.LdpEval.ldpLo, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, Sail.BitVec.castWidth,
    dite_true, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast]
  rw [BitVec.append_eq, BitVec.getLsbD_append]
  simp [hi']

theorem ldpLo_stpData (s : NativeState) :
    ArmCertMem.LdpEval.ldpLo (ArmCertMem.StpEval.stpData s 9#5 30#5) = s.regs.gpr[9] := by
  unfold ArmCertMem.StpEval.stpData
  exact ldpLo_append _ _
theorem next_placed {x : NativeState} {base : BitVec 64} {offS : Nat → BitVec 64} {j : Nat}
    (pc : x.regs._PC = base + offS j) (hs : offS (j + 1) = offS j + 4#64) :
    x.regs._PC + 4#64 = base + offS (j + 1) := by
  rw [pc, hs, BitVec.add_assoc]

theorem enc_bit (d : BitVec 1) : (((0#39 +++ d) +++ 0#24).extractLsb 24 24) = d := by
  have h := d.isLt
  rcases (show d = 0#1 ∨ d = 1#1 by
    by_cases h0 : d.toNat = 0
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h0]))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simp; omega))) with rfl | rfl <;> decide
end DitShim243.Utils
