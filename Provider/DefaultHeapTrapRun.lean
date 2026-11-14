import DefaultHeapTrapSteps
import RtT.TrapT
import Bridge.CruxGenGuarded.EvSteps.CT
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open HeapV2StepCerts CertiFFI.Prog.Generic.ModelRunView
open RtBl.Trap
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultHeapTrap

theorem plain_step {real : Type} [Sail.SailReal real] {domain : QueryDomain}
    {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {I J : NativeState → Prop} (step : DefaultHeapResidue.Step real spec mapping [] I J) :
    Uget.Chain.Step real I J := by
  intro x hx
  obtain ⟨fin, run, next, _, _⟩ := step x hx
  exact ⟨fin, run, next⟩


theorem trap0_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 1 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 1 → ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ true = true))
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 1 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 1).regs._PC = base + trapOffset ∧
    (∀ k, k < 1 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) := by
  have steps : ∀ k, k < 1 → DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 := by omega
        rcases hk' with rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 1) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 true
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
  have init : BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) k x ∧ V k x) 1 (fun k hk => plain_step (steps k hk)) entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) k x ∧ V k x) 1 entry (fun k hk => plain_step (steps k hk)) init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.core.v1.pins, h.1.core.v1.features, h.1.core.v1.debug,
      h.1.core.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.core.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_, ?_⟩
  · have pc := (inv 1 (Nat.le_refl _)).1.core.v1.pc
    rw [pc]; simp [trapOff]
  · intro k hk
    obtain ⟨fin, run, _, _, events⟩ := steps k hk _ (inv k (by omega))
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact events

#print axioms trap0_runV

theorem trap1_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 2 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 2 → ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ true = true))
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 2 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 2).regs._PC = base + trapOffset ∧
    (∀ k, k < 2 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) := by
  have steps : ∀ k, k < 2 → DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 2) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 2) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 true
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
  have init : BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) k x ∧ V k x) 2 (fun k hk => plain_step (steps k hk)) entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) k x ∧ V k x) 2 entry (fun k hk => plain_step (steps k hk)) init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.core.v1.pins, h.1.core.v1.features, h.1.core.v1.debug,
      h.1.core.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.core.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_, ?_⟩
  · have pc := (inv 2 (Nat.le_refl _)).1.core.v1.pc
    rw [pc]; simp [trapOff]
  · intro k hk
    obtain ⟨fin, run, _, _, events⟩ := steps k hk _ (inv k (by omega))
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact events

#print axioms trap1_runV

theorem trap2_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 4 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 4 → ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) 3 x → V 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 4 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 4).regs._PC = base + trapOffset ∧
    (∀ k, k < 4 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) := by
  have steps : ∀ k, k < 4 → DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk' with rfl | rfl | rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 4) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 4) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 false
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 4) 2
            (by simp [trapOff]) (by simp [trapOff])
            (rich_2 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 2 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 4) 3 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 176#19 true
            (by decide) 12 1409291777 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
            (vcarry 3 (by omega))
  have init : BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) k x ∧ V k x) 4 (fun k hk => plain_step (steps k hk)) entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) k x ∧ V k x) 4 entry (fun k hk => plain_step (steps k hk)) init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.core.v1.pins, h.1.core.v1.features, h.1.core.v1.debug,
      h.1.core.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.core.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_, ?_⟩
  · have pc := (inv 4 (Nat.le_refl _)).1.core.v1.pc
    rw [pc]; simp [trapOff]
  · intro k hk
    obtain ⟨fin, run, _, _, events⟩ := steps k hk _ (inv k (by omega))
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact events

#print axioms trap2_runV

theorem trap3_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 6 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 6 → ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) 3 x → V 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) 5 x → V 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 6 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 6).regs._PC = base + trapOffset ∧
    (∀ k, k < 6 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) := by
  have steps : ∀ k, k < 6 → DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 6) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 6) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 false
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 6) 2
            (by simp [trapOff]) (by simp [trapOff])
            (rich_2 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 2 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 6) 3 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 176#19 false
            (by decide) 12 1409291777 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
            (vcarry 3 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 6) 4
            (by simp [trapOff]) (by simp [trapOff])
            (rich_4 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 4 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 6) 5 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 174#19 true
            (by decide) 20 1409291713 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5
            (vcarry 5 (by omega))
  have init : BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) k x ∧ V k x) 6 (fun k hk => plain_step (steps k hk)) entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) k x ∧ V k x) 6 entry (fun k hk => plain_step (steps k hk)) init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.core.v1.pins, h.1.core.v1.features, h.1.core.v1.debug,
      h.1.core.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.core.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_, ?_⟩
  · have pc := (inv 6 (Nat.le_refl _)).1.core.v1.pc
    rw [pc]; simp [trapOff]
  · intro k hk
    obtain ⟨fin, run, _, _, events⟩ := steps k hk _ (inv k (by omega))
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact events

#print axioms trap3_runV

theorem trap4_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 8 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 8 → ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) 3 x → V 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) 5 x → V 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_7 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) 7 x → V 7 x →
      (Crypto.BcondCore.bcondC 3#4 x.regs ↔ true = true))
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 8 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 8).regs._PC = base + trapOffset ∧
    (∀ k, k < 8 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) := by
  have steps : ∀ k, k < 8 → DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 8) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 8) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 false
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 8) 2
            (by simp [trapOff]) (by simp [trapOff])
            (rich_2 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 2 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 8) 3 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 176#19 false
            (by decide) 12 1409291777 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
            (vcarry 3 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 8) 4
            (by simp [trapOff]) (by simp [trapOff])
            (rich_4 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 4 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 8) 5 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 174#19 false
            (by decide) 20 1409291713 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5
            (vcarry 5 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 8) 6
            (by simp [trapOff]) (by simp [trapOff])
            (rich_6 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 6 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 8) 7 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 3#4 172#19 true
            (by decide) 28 1409291651 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 7 + sign_extend (172#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_7
            (vcarry 7 (by omega))
  have init : BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) k x ∧ V k x) 8 (fun k hk => plain_step (steps k hk)) entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) k x ∧ V k x) 8 entry (fun k hk => plain_step (steps k hk)) init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.core.v1.pins, h.1.core.v1.features, h.1.core.v1.debug,
      h.1.core.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.core.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_, ?_⟩
  · have pc := (inv 8 (Nat.le_refl _)).1.core.v1.pc
    rw [pc]; simp [trapOff]
  · intro k hk
    obtain ⟨fin, run, _, _, events⟩ := steps k hk _ (inv k (by omega))
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact events

#print axioms trap4_runV

theorem trap5_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 10 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 10 → ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) 3 x → V 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) 5 x → V 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_7 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) 7 x → V 7 x →
      (Crypto.BcondCore.bcondC 3#4 x.regs ↔ false = true))
    (dec_9 : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) 9 x → V 9 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 10 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 10).regs._PC = base + trapOffset ∧
    (∀ k, k < 10 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) := by
  have steps : ∀ k, k < 10 → DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 false
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 2
            (by simp [trapOff]) (by simp [trapOff])
            (rich_2 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 2 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 3 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 176#19 false
            (by decide) 12 1409291777 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
            (vcarry 3 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 4
            (by simp [trapOff]) (by simp [trapOff])
            (rich_4 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 4 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 5 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 174#19 false
            (by decide) 20 1409291713 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5
            (vcarry 5 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 6
            (by simp [trapOff]) (by simp [trapOff])
            (rich_6 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 6 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 7 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 3#4 172#19 false
            (by decide) 28 1409291651 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 7 + sign_extend (172#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_7
            (vcarry 7 (by omega))
        · exact straightV real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 8
            (by simp [trapOff]) (by simp [trapOff])
            (rich_8 real spec config rows mapping base budget pins table S catalogue entry static (by omega) page nodup)
            (vcarry 8 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table S catalogue entry static nodup V (trapOff 10) 9 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 170#19 true
            (by decide) 36 1409291585 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 9 + sign_extend (170#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_9
            (vcarry 9 (by omega))
  have init : BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) k x ∧ V k x) 10 (fun k hk => plain_step (steps k hk)) entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) k x ∧ V k x) 10 entry (fun k hk => plain_step (steps k hk)) init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.core.v1.pins, h.1.core.v1.features, h.1.core.v1.debug,
      h.1.core.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.core.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_, ?_⟩
  · have pc := (inv 10 (Nat.le_refl _)).1.core.v1.pc
    rw [pc]; simp [trapOff]
  · intro k hk
    obtain ⟨fin, run, _, _, events⟩ := steps k hk _ (inv k (by omega))
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact events

#print axioms trap5_runV

end ReleaseProfile.DefaultHeapTrap
