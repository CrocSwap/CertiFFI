-- Memory (/, H-P2): CT2 frame residue along the heap-v2 normal-path run, any deployment.
import HeapV2StepCerts.Residue.RSeg_00
import HeapV2StepCerts.Residue.RSeg_01
import HeapV2StepCerts.Residue.RSeg_02
import HeapV2StepCerts.Residue.RSeg_03
import HeapV2StepCerts.Residue.RSeg_04
import HeapV2StepCerts.Residue.RSeg_05
import HeapV2StepCerts.Residue.RSeg_06
import HeapV2StepCerts.Residue.RSeg_07
import HeapV2StepCerts.Residue.RSeg_08
import HeapV2StepCerts.Residue.RSeg_09
import HeapV2StepCerts.Residue.RSeg_10
import HeapV2StepCerts.Residue.RSeg_11
import HeapV2StepCerts.Residue.RMemSeg_00
import HeapV2StepCerts.Residue.RMemSeg_01
import HeapV2StepCerts.Residue.RMemSeg_02
import HeapV2StepCerts.Residue.RMemSeg_03
import HeapV2StepCerts.Residue.RMemSeg_04
import HeapV2StepCerts.Residue.RMemSeg_05
import HeapV2StepCerts.E17General.Assembly
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.Residue.Run
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem memSteps5 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) : MemStepsG5 real spec config rows mapping base pins entry budget := by
  intro k hk hm
  rcases (show (0 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact memSeg_00 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_01 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_02 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_03 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_04 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_05 real spec config rows mapping base pins entry budget dp hb k lo hi hm

theorem steps5 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) :
    ∀ k, k < 357 → Uget.Chain.Step real (I5 spec config rows mapping base pins entry budget k) (I5 spec config rows mapping base pins entry budget (k + 1)) := by
  have mem := memSteps5 real spec config rows mapping base pins entry budget dp hb
  intro k hk
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact seg_00 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_01 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_02 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_03 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_04 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_05 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_06 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_07 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_08 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_09 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_10 real spec config rows mapping base pins entry budget dp hb mem k lo hi
  · exact seg_11 real spec config rows mapping base pins entry budget dp hb mem k lo hi

/-- The residue along the run: every reached state k ≤ 357 satisfies ChainInv v4 and Res. -/
theorem residue_general (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) : ∀ k, k ≤ 357 → I5 spec config rows mapping base pins entry budget k (stateAt real entry k) :=
  CertiFFI.Prog.Generic.ModelRunView.invariant_prefixes real (I5 spec config rows mapping base pins entry budget) 357 (steps5 real spec config rows mapping base pins entry budget dp hb) entry
    ⟨initialG budget dp, Residue.resL_entry pins mapping base entry⟩

/-- **H-P2 ct2Residue_run** (heap-v2 normal path, any deployment satisfying DeploymentPremises), at the final RET
state k = 357: X18 and X20..X29 equal entry; X30 equals entry (lrSaved); X19 equals entry (RtSaved3 / LdpPay2); SP equals entry SP; every memory byte
outside the plan's store bytes (StoreBytes = the output buffer via x0 ∪ the stack frame via SP, store_pins) equals
its entry value. -/
theorem ct2Residue_run (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) :
    let fin := stateAt real entry 357
    (∀ r ∈ Residue.frameRegs, RegBind.regVal fin (.x r) = RegBind.regVal entry (.x r)) ∧
    fin.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = entry.regs.gpr[30] ∧
    fin.regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = entry.regs.gpr[19] ∧
    fin.regs.SP_EL0 = entry.regs.SP_EL0 ∧
    (∀ a, ¬ Residue.StoreBytes pins mapping a → fin.mem[a]? = entry.mem[a]?) := by
  intro fin
  have h := residue_general real spec config rows mapping base pins entry budget dp hb 357 (Nat.le_refl _)
  have h0 := initialG budget dp
  have sp0 := h0.v3.regBind (.sp, 0, 0) (by decide +kernel)
  have sp357 := h.1.v3.regBind (.sp, 0, 0) (by decide +kernel)
  simp only [RegBind.regVal] at sp0 sp357
  exact ⟨h.2.1.1, lrSaved_of_v4 h.1, RtSaved3.x19_of_chain h.2.2, sp357.trans sp0.symm, h.2.1.2⟩

#print axioms residue_general
#print axioms ct2Residue_run
end HeapV2StepCerts.Residue.Run
