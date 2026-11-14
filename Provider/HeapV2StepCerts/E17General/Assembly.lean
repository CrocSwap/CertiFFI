-- Memory: E17 heap-v2 normal path for an ARBITRARY deployment satisfying DeploymentPremises.
-- Assembly of the generalized segments (gen_e17general.py from certiffi's E17Synth, 6194db87).
import HeapV2StepCerts.E17General.Seg_00
import HeapV2StepCerts.E17General.Seg_01
import HeapV2StepCerts.E17General.Seg_02
import HeapV2StepCerts.E17General.Seg_03
import HeapV2StepCerts.E17General.Seg_04
import HeapV2StepCerts.E17General.Seg_05
import HeapV2StepCerts.E17General.Seg_06
import HeapV2StepCerts.E17General.Seg_07
import HeapV2StepCerts.E17General.Seg_08
import HeapV2StepCerts.E17General.Seg_09
import HeapV2StepCerts.E17General.Seg_10
import HeapV2StepCerts.E17General.Seg_11
import HeapV2StepCerts.E17General.MemSeg_00
import HeapV2StepCerts.E17General.MemSeg_01
import HeapV2StepCerts.E17General.MemSeg_02
import HeapV2StepCerts.E17General.MemSeg_03
import HeapV2StepCerts.E17General.MemSeg_04
import HeapV2StepCerts.E17General.MemSeg_05
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.E17General
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem memStepsG (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) : MemStepsG real spec config rows mapping base pins entry budget := by
  intro k hk hm
  rcases (show (0 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact memSeg_00 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_01 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_02 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_03 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_04 real spec config rows mapping base pins entry budget dp hb k lo hi hm
  · exact memSeg_05 real spec config rows mapping base pins entry budget dp hb k lo hi hm

theorem stepsG (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) :
    ∀ k, k < 357 → Uget.Chain.Step real (I4 spec config rows mapping base pins entry budget k) (I4 spec config rows mapping base pins entry budget (k + 1)) := by
  have mem := memStepsG real spec config rows mapping base pins entry budget dp hb
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

/-- **E17, heap-v2 normal path, any deployment.** For every deployment and entry state satisfying
DeploymentPremises, every reached state k ≤ 357 of the ACTUAL model run satisfies ChainInv v4 and E17
TranslationAgrees (consumerMap pins base mapping table-footprint), and at the final RET X30 is the entry X30. -/
theorem e17_general (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) :
    (∀ k, k ≤ 357 →
      I4 spec config rows mapping base pins entry budget k (stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (cmap spec mapping base pins) (stateAt real entry k)) ∧
    (stateAt real entry 357).regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = entry.regs.gpr[30] := by
  have run := path_run4 real spec config rows mapping _ dp.agrees HeapV2StepCerts.codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins (qOf entry) _ _ 357 (stepsG real spec config rows mapping base pins entry budget dp hb) entry (initialG budget dp)
  exact ⟨run, lrSaved_of_v4 (run 357 (Nat.le_refl _)).1⟩

#print axioms memStepsG
#print axioms stepsG
#print axioms e17_general
end HeapV2StepCerts.E17General
