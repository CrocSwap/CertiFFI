-- Memory (H-P2,): V8..V15 (the whole SIMD file _Z) and the scrub constants at the RET state 357.
-- zSteps (per-step ZStep, ZSeg_NN), threaded along e17_general's run with residue_general (I4 at every k) by
-- determinism of modelStep; ct2Residue_full = ct2Residue_run + _Z = entry _Z + x0..x17 = 0 + PSTATE.Z = 1.
import HeapV2StepCerts.Residue.ZSeg_00
import HeapV2StepCerts.Residue.ZSeg_01
import HeapV2StepCerts.Residue.ZSeg_02
import HeapV2StepCerts.Residue.ZSeg_03
import HeapV2StepCerts.Residue.ZSeg_04
import HeapV2StepCerts.Residue.ZSeg_05
import HeapV2StepCerts.Residue.ZSeg_06
import HeapV2StepCerts.Residue.ZSeg_07
import HeapV2StepCerts.Residue.ZSeg_08
import HeapV2StepCerts.Residue.ZSeg_09
import HeapV2StepCerts.Residue.ZSeg_10
import HeapV2StepCerts.Residue.ZSeg_11
import HeapV2StepCerts.Residue.RAssembly
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.ZSteps
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open CertiFFI.Prog.Generic.ModelRunView ArmBridge.Boundary ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem zSteps (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k < 357 → ZStep real spec config rows mapping base pins entry budget k := by
  intro k hk
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact zSeg_00 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_01 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_02 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_03 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_04 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_05 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_06 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_07 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_08 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_09 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_10 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact zSeg_11 real spec config rows mapping base pins entry budget dp hb k lo hi

theorem stateAt_succ {real : Type} [Sail.SailReal real] {s fin : NativeState} {k : Nat}
    (run : modelStep real (stateAt real s k) = .ok () fin) : stateAt real s (k + 1) = fin := by
  show next real (stateAt real s k) = fin
  unfold next; rw [run]

/-- Along the run: the SIMD file is the entry's, and PSTATE.Z = 1 on 351..357 (ZBind). -/
theorem residue_z (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k ≤ 357 → (stateAt real entry k).regs._Z = entry.regs._Z ∧ HeapV2StepCerts.ValBind.ZBind k (stateAt real entry k) ∧
      NCVBind k (stateAt real entry k) := by
  have hres := Residue.Run.residue_general real spec config rows mapping base pins entry budget dp hb
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, HeapV2StepCerts.ValBind.zbind_init _, ncv_init _⟩
  | succ k ih =>
    intro hk
    obtain ⟨z0, zb, nb⟩ := ih (by omega)
    obtain ⟨fin, run, z, f350, fl⟩ := zSteps real spec config rows mapping base pins entry budget dp hb k (by omega)
      (stateAt real entry k) (hres k (by omega)).1
    rw [stateAt_succ run]
    refine ⟨z.trans z0, ?_⟩
    by_cases h350 : k = 350
    · subst h350
      exact ⟨HeapV2StepCerts.ValBind.zbind_350 (hres 350 (by omega)).1.valBind (f350 rfl).1, fun _ _ => (f350 rfl).2⟩
    · by_cases hr : 351 ≤ k ∧ k ≤ 356
      · exact ⟨HeapV2StepCerts.ValBind.zbind_keep hr.1 zb (fl hr.1 hr.2), ncv_keep hr.1 nb (fl hr.1 hr.2)⟩
      · exact ⟨HeapV2StepCerts.ValBind.zbind_out fin (by omega), ncv_out fin (by omega)⟩

/-- **H-P2 ct2Residue (full)** at the RET state 357: ct2Residue_run (frame regs X18/X20..X29, X30, X19, SP, memory
outside the store bytes = entry) plus the SIMD file (so V8..V15) = entry, the scrubbed x0..x17 = 0 and NZCV = 0100. -/
theorem ct2Residue_full (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    (∀ r ∈ Residue.frameRegs, RegBind.regVal (stateAt real entry 357) (.x r) = RegBind.regVal entry (.x r)) ∧
    (stateAt real entry 357).regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = entry.regs.gpr[30] ∧
    (stateAt real entry 357).regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = entry.regs.gpr[19] ∧
    (stateAt real entry 357).regs.SP_EL0 = entry.regs.SP_EL0 ∧
    (∀ a, ¬ Residue.StoreBytes pins mapping a → (stateAt real entry 357).mem[a]? = entry.mem[a]?) ∧
    (stateAt real entry 357).regs._Z = entry.regs._Z ∧
    (∀ i : Fin 18, RegBind.regVal (stateAt real entry 357) (.x (Fin.castLE (by decide) i)) = 0#64) ∧
    (stateAt real entry 357).regs.PSTATE.Z = 1#1 ∧
    (stateAt real entry 357).regs.PSTATE.N = 0#1 ∧ (stateAt real entry 357).regs.PSTATE.C = 0#1 ∧
    (stateAt real entry 357).regs.PSTATE.V = 0#1 := by
  have h := Residue.Run.ct2Residue_run real spec config rows mapping base pins entry budget dp hb
  have hz := residue_z real spec config rows mapping base pins entry budget dp hb 357 (Nat.le_refl _)
  have hres := Residue.Run.residue_general real spec config rows mapping base pins entry budget dp hb 357 (Nat.le_refl _)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hz.1,
    HeapV2StepCerts.ValBind.scrub_at_357 hres.1.valBind, hz.2.1 (by decide) (by decide), hz.2.2 (by decide) (by decide)⟩

#print axioms zSteps
#print axioms residue_z
#print axioms ct2Residue_full
end HeapV2StepCerts.ZSteps
