-- trap paths 0 and 1 (L = 1, 2) generic in the consumer map m
-- (Core instantiates m := consumerMapOn (fun _ => False) ..: code fetches only). Same shape as RtT.TrapT
-- (ChainInv3 (trapOff L) ∧ ValBindT L q, decisions decT_L_k), but the fetch obligations are hypotheses
-- fetch_k (Core: Memory's memFetchOn) instead of memFetch over the full consumerMap.
import RtT.TrapV
import HeapV2StepCerts.ValBindTrapSteps
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV3 ArmBridge.CruxGenGuarded.ChainInv
open RtBl.Trap HeapV2StepCerts.ValBind CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace RtBl.TrapG

/-- A guard CBZ at k under `off`, generic consumer map m, fetch obligations supplied. -/
theorem brStepG_cbz (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
    (off : Nat → BitVec 64) (k : Nat) (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (hereN : off k = HeapV2Compose.offsetOf k) (aligned : (off k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = []) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (Rt : BitVec 5) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyCbz.W Rt imm19) 31 12 == 879088#20) = false)
    (land : off (k + 1) = if taken then HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64 else HeapV2Compose.offsetOf k + 4#64)
    (lowT : (base + (HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (fetch : ∀ x, ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x → FetchObligations spec config rows mapping (EntryBodyCbz.W Rt imm19) x)
    (dec : ∀ x, ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x → V k x → (Crypto.CruxCbz.cbzC 1#1 Rt x ↔ taken = true))
    (vc : ∀ s f, ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f) :
    Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins (k + 1) x ∧ V (k + 1) x) := by
  intro x ⟨inv, v⟩
  obtain ⟨fin, run, inv', r⟩ := RtB2.RichG.rich_branch_cbz_at real spec config rows mapping m HeapV2StepCerts.codeScope
    (HeapV2.image base) base static.separated base off budget pins k room hk page aligned upd0 veff Rt imm19 taken
    noEret x inv (dec x inv v)
    (fun x inv => by rw [inv.v2.v1.pc, hereN, BitVec.add_assoc]; exact lowT)
    (fun x inv => by rw [inv.v2.v1.pc, hereN, land]; cases taken <;> simp [BitVec.add_assoc])
    fetch
  exact ⟨fin, run, inv', vc x fin inv v r.1 r.2.1⟩

/-- Trap path 0 (L = 1) over ChainInv3 m (trapOff 1) ∧ ValBindT 1 q, generic consumer map m. -/
theorem trap0_runG (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping m)
    (room : 1 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 1 pins q)
    (fetch_0 : ∀ x, ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins 0 x →
      FetchObligations spec config rows mapping (EntryBodyCbz.W 0#5 179#19) x)
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : ValBindT 1 q 0 entry) :
    (∀ k, k ≤ 1 → (ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k (stateAt real entry k) ∧ (k < 1 → ValBindT 1 q k (stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m (stateAt real entry k)) ∧
    (stateAt real entry 1).regs._PC = base + trapOffset := by
  have steps : ∀ k, k < 1 → Uget.Chain.Step real ((fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k x ∧ (k < 1 → ValBindT 1 q k x)) k) ((fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k x ∧ (k < 1 → ValBindT 1 q k x)) (k + 1)) := by
    intro k hk
    have hk' : k = 0 := by omega
    rcases hk' with rfl
    · exact brStepG_cbz real spec config rows mapping m base budget pins static (fun k x => k < 1 → ValBindT 1 q k x)
        (trapOff 1) 0 (by omega) (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 true
        (by decide) (by decide +kernel)
        (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716)
        fetch_0 (fun x inv v => decT_1_0 np inv.regBind (v (by decide)))
        (fun s f inv v holds eff hlt => absurd hlt (by decide))
  have init : (fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k x ∧ (k < 1 → ValBindT 1 q k x)) 0 entry := ⟨inv_congr initial (by simp [trapOff]), fun _ => initialV⟩
  have inv := invariant_prefixes real (fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k x ∧ (k < 1 → ValBindT 1 q k x)) 1 steps entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping m agrees (fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k x ∧ (k < 1 → ValBindT 1 q k x)) 1 entry steps init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.v2.v1.pins, h.1.v2.v1.features, h.1.v2.v1.debug,
      h.1.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.v2.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_⟩
  have pc := (inv 1 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 1 (L = 2) over ChainInv3 m (trapOff 2) ∧ ValBindT 2 q, generic consumer map m. -/
theorem trap1_runG (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping m)
    (room : 2 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 2 pins q)
    (fetch_0 : ∀ x, ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins 0 x →
      FetchObligations spec config rows mapping (EntryBodyCbz.W 0#5 179#19) x)
    (fetch_1 : ∀ x, ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins 1 x →
      FetchObligations spec config rows mapping (EntryBodyCbz.W 1#5 178#19) x)
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : ValBindT 2 q 0 entry) :
    (∀ k, k ≤ 2 → (ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k (stateAt real entry k) ∧ (k < 2 → ValBindT 2 q k (stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m (stateAt real entry k)) ∧
    (stateAt real entry 2).regs._PC = base + trapOffset := by
  have steps : ∀ k, k < 2 → Uget.Chain.Step real ((fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k x ∧ (k < 2 → ValBindT 2 q k x)) k) ((fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k x ∧ (k < 2 → ValBindT 2 q k x)) (k + 1)) := by
    intro k hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · exact brStepG_cbz real spec config rows mapping m base budget pins static (fun k x => k < 2 → ValBindT 2 q k x)
        (trapOff 2) 0 (by omega) (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
        (by decide) (by decide +kernel)
        (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716)
        fetch_0 (fun x inv v => decT_2_0 np inv.regBind (v (by decide)))
        (fun s f inv v holds eff hlt => carryT_2_0 np inv.regBind (v (by decide)) holds eff)
    · exact brStepG_cbz real spec config rows mapping m base budget pins static (fun k x => k < 2 → ValBindT 2 q k x)
        (trapOff 2) 1 (by omega) (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 true
        (by decide) (by decide +kernel)
        (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716)
        fetch_1 (fun x inv v => decT_2_1 np inv.regBind (v (by decide)))
        (fun s f inv v holds eff hlt => absurd hlt (by decide))
  have init : (fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k x ∧ (k < 2 → ValBindT 2 q k x)) 0 entry := ⟨inv_congr initial (by simp [trapOff]), fun _ => initialV⟩
  have inv := invariant_prefixes real (fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k x ∧ (k < 2 → ValBindT 2 q k x)) 2 steps entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping m agrees (fun k x => ChainInv3 spec config rows mapping m HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k x ∧ (k < 2 → ValBindT 2 q k x)) 2 entry steps init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.v2.v1.pins, h.1.v2.v1.features, h.1.v2.v1.debug,
      h.1.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.v2.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_⟩
  have pc := (inv 2 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

#print axioms brStepG_cbz
#print axioms trap0_runG
#print axioms trap1_runG
end RtBl.TrapG
