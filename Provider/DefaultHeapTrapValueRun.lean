import DefaultHeapTrapRun
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open HeapV2StepCerts CertiFFI.Prog.Generic.ModelRunView
open RtBl.Trap HeapV2StepCerts.ValBind
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultHeapTrap


theorem trap0_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 1 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 1 pins q)
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : ValBindT 1 q 0 entry) :
    (∀ k, k ≤ 1 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 1) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 1 → ValBindT 1 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 1).regs._PC = base + trapOffset ∧
    (∀ k, k < 1 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) :=
  trap0_runV real spec config rows mapping base budget pins table S catalogue entry static nodup
    (fun k x => k < 1 → ValBindT 1 q k x) agrees room page low716
    (by intro k hk s f inv v holds eff hlt; omega)
    (fun x inv v => decT_1_0 np inv.regBind (v (by decide)))
    initial (fun _ => initialV)

#print axioms trap0_runT

theorem trap1_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 2 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 2 pins q)
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : ValBindT 2 q 0 entry) :
    (∀ k, k ≤ 2 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 2) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 2 → ValBindT 2 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 2).regs._PC = base + trapOffset ∧
    (∀ k, k < 2 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) :=
  trap1_runV real spec config rows mapping base budget pins table S catalogue entry static nodup
    (fun k x => k < 2 → ValBindT 2 q k x) agrees room page low716
    (by
      intro k hk s f inv v holds eff hlt
      have hk' : k = 0 := by omega
      rcases hk' with rfl
      · exact carryT_2_0 np inv.regBind (v (by decide)) holds eff)
    (fun x inv v => decT_2_0 np inv.regBind (v (by decide))) (fun x inv v => decT_2_1 np inv.regBind (v (by decide)))
    initial (fun _ => initialV)

#print axioms trap1_runT

theorem trap2_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 4 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 4 pins q)
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : ValBindT 4 q 0 entry) :
    (∀ k, k ≤ 4 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 4) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 4 → ValBindT 4 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 4).regs._PC = base + trapOffset ∧
    (∀ k, k < 4 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) :=
  trap2_runV real spec config rows mapping base budget pins table S catalogue entry static nodup
    (fun k x => k < 4 → ValBindT 4 q k x) agrees room page low716
    (by
      intro k hk s f inv v holds eff hlt
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl | rfl
      · exact carryT_4_0 np inv.regBind (v (by decide)) holds eff
      · exact carryT_4_1 np inv.regBind (v (by decide)) holds eff
      · exact carryT_4_2 np inv.regBind (v (by decide)) holds eff)
    (fun x inv v => decT_4_0 np inv.regBind (v (by decide))) (fun x inv v => decT_4_1 np inv.regBind (v (by decide))) (fun x inv v => decT_4_3 np inv.regBind (v (by decide)))
    initial (fun _ => initialV)

#print axioms trap2_runT

theorem trap3_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 6 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 6 pins q)
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : ValBindT 6 q 0 entry) :
    (∀ k, k ≤ 6 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 6) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 6 → ValBindT 6 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 6).regs._PC = base + trapOffset ∧
    (∀ k, k < 6 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) :=
  trap3_runV real spec config rows mapping base budget pins table S catalogue entry static nodup
    (fun k x => k < 6 → ValBindT 6 q k x) agrees room page low716
    (by
      intro k hk s f inv v holds eff hlt
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk' with rfl | rfl | rfl | rfl | rfl
      · exact carryT_6_0 np inv.regBind (v (by decide)) holds eff
      · exact carryT_6_1 np inv.regBind (v (by decide)) holds eff
      · exact carryT_6_2 np inv.regBind (v (by decide)) holds eff
      · exact carryT_6_3 np inv.regBind (v (by decide)) holds eff
      · exact carryT_6_4 np inv.regBind (v (by decide)) holds eff)
    (fun x inv v => decT_6_0 np inv.regBind (v (by decide))) (fun x inv v => decT_6_1 np inv.regBind (v (by decide))) (fun x inv v => decT_6_3 np inv.regBind (v (by decide))) (fun x inv v => decT_6_5 np inv.regBind (v (by decide)))
    initial (fun _ => initialV)

#print axioms trap3_runT

theorem trap4_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 8 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 8 pins q)
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : ValBindT 8 q 0 entry) :
    (∀ k, k ≤ 8 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 8) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 8 → ValBindT 8 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 8).regs._PC = base + trapOffset ∧
    (∀ k, k < 8 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) :=
  trap4_runV real spec config rows mapping base budget pins table S catalogue entry static nodup
    (fun k x => k < 8 → ValBindT 8 q k x) agrees room page low716
    (by
      intro k hk s f inv v holds eff hlt
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact carryT_8_0 np inv.regBind (v (by decide)) holds eff
      · exact carryT_8_1 np inv.regBind (v (by decide)) holds eff
      · exact carryT_8_2 np inv.regBind (v (by decide)) holds eff
      · exact carryT_8_3 np inv.regBind (v (by decide)) holds eff
      · exact carryT_8_4 np inv.regBind (v (by decide)) holds eff
      · exact carryT_8_5 np inv.regBind (v (by decide)) holds eff
      · exact carryT_8_6 np inv.regBind (v (by decide)) holds eff)
    (fun x inv v => decT_8_0 np inv.regBind (v (by decide))) (fun x inv v => decT_8_1 np inv.regBind (v (by decide))) (fun x inv v => decT_8_3 np inv.regBind (v (by decide))) (fun x inv v => decT_8_5 np inv.regBind (v (by decide))) (fun x inv v => decT_8_7 np inv.regBind (v (by decide)))
    initial (fun _ => initialV)

#print axioms trap4_runT

theorem trap5_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table))
    (room : 10 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 10 pins q)
    (initial : BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 0 entry) (initialV : ValBindT 10 q 0 entry) :
    (∀ k, k ≤ 10 → (BaseInv spec config rows mapping S base budget pins table catalogue entry (trapOff 10) k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 10 → ValBindT 10 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 10).regs._PC = base + trapOffset ∧
    (∀ k, k < 10 → StepEvents.EvShape spec mapping []
      (stateAt real entry k) (stateAt real entry (k + 1))) :=
  trap5_runV real spec config rows mapping base budget pins table S catalogue entry static nodup
    (fun k x => k < 10 → ValBindT 10 q k x) agrees room page low716
    (by
      intro k hk s f inv v holds eff hlt
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact carryT_10_0 np inv.regBind (v (by decide)) holds eff
      · exact carryT_10_1 np inv.regBind (v (by decide)) holds eff
      · exact carryT_10_2 np inv.regBind (v (by decide)) holds eff
      · exact carryT_10_3 np inv.regBind (v (by decide)) holds eff
      · exact carryT_10_4 np inv.regBind (v (by decide)) holds eff
      · exact carryT_10_5 np inv.regBind (v (by decide)) holds eff
      · exact carryT_10_6 np inv.regBind (v (by decide)) holds eff
      · exact carryT_10_7 np inv.regBind (v (by decide)) holds eff
      · exact carryT_10_8 np inv.regBind (v (by decide)) holds eff)
    (fun x inv v => decT_10_0 np inv.regBind (v (by decide))) (fun x inv v => decT_10_1 np inv.regBind (v (by decide))) (fun x inv v => decT_10_3 np inv.regBind (v (by decide))) (fun x inv v => decT_10_5 np inv.regBind (v (by decide))) (fun x inv v => decT_10_7 np inv.regBind (v (by decide))) (fun x inv v => decT_10_9 np inv.regBind (v (by decide)))
    initial (fun _ => initialV)

#print axioms trap5_runT

end ReleaseProfile.DefaultHeapTrap
