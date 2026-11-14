-- trap runs v2 over TrapInv L:= ChainInv3 (trapOff L) ∧ ValBindT L q.
-- Instances of RtBl.TrapV.trapJ_runV with V k x := k < L → ValBindT L q k x (the trap endpoint carries no
-- binding), decisions decT_L_k and carries carryT_L_k from Memory's stepcerts-trap (7a4701eb), under TrapPath L.
import RtT.TrapV
import HeapV2StepCerts.ValBindTrapSteps
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV3
open RtBl.Trap HeapV2StepCerts.ValBind
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace RtBl.TrapT

/-- Trap path 0 (L = 1) over ChainInv3 (trapOff 1) ∧ ValBindT 1 q, under TrapPath 1 pins q. -/
theorem trap0_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 1 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 1 pins q)
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : ValBindT 1 q 0 entry) :
    (∀ k, k ≤ 1 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 1 → ValBindT 1 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 1).regs._PC = base + trapOffset :=
  RtBl.TrapV.trap0_runV real spec config rows mapping base budget pins table static
    (fun k x => k < 1 → ValBindT 1 q k x) agrees room page low716
    (by intro k hk s f inv v holds eff hlt; omega)
    (fun x inv v => decT_1_0 np inv.regBind (v (by decide)))
    entry initial (fun _ => initialV)

/-- Trap path 1 (L = 2) over ChainInv3 (trapOff 2) ∧ ValBindT 2 q, under TrapPath 2 pins q. -/
theorem trap1_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 2 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 2 pins q)
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : ValBindT 2 q 0 entry) :
    (∀ k, k ≤ 2 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 2 → ValBindT 2 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 2).regs._PC = base + trapOffset :=
  RtBl.TrapV.trap1_runV real spec config rows mapping base budget pins table static
    (fun k x => k < 2 → ValBindT 2 q k x) agrees room page low716
    (by
      intro k hk s f inv v holds eff hlt
      have hk' : k = 0 := by omega
      rcases hk' with rfl
      · exact carryT_2_0 np inv.regBind (v (by decide)) holds eff)
    (fun x inv v => decT_2_0 np inv.regBind (v (by decide))) (fun x inv v => decT_2_1 np inv.regBind (v (by decide)))
    entry initial (fun _ => initialV)

/-- Trap path 2 (L = 4) over ChainInv3 (trapOff 4) ∧ ValBindT 4 q, under TrapPath 4 pins q. -/
theorem trap2_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 4 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 4 pins q)
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : ValBindT 4 q 0 entry) :
    (∀ k, k ≤ 4 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 4 → ValBindT 4 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 4).regs._PC = base + trapOffset :=
  RtBl.TrapV.trap2_runV real spec config rows mapping base budget pins table static
    (fun k x => k < 4 → ValBindT 4 q k x) agrees room page low716
    (by
      intro k hk s f inv v holds eff hlt
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl | rfl
      · exact carryT_4_0 np inv.regBind (v (by decide)) holds eff
      · exact carryT_4_1 np inv.regBind (v (by decide)) holds eff
      · exact carryT_4_2 np inv.regBind (v (by decide)) holds eff)
    (fun x inv v => decT_4_0 np inv.regBind (v (by decide))) (fun x inv v => decT_4_1 np inv.regBind (v (by decide))) (fun x inv v => decT_4_3 np inv.regBind (v (by decide)))
    entry initial (fun _ => initialV)

/-- Trap path 3 (L = 6) over ChainInv3 (trapOff 6) ∧ ValBindT 6 q, under TrapPath 6 pins q. -/
theorem trap3_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 6 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 6 pins q)
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : ValBindT 6 q 0 entry) :
    (∀ k, k ≤ 6 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 6 → ValBindT 6 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 6).regs._PC = base + trapOffset :=
  RtBl.TrapV.trap3_runV real spec config rows mapping base budget pins table static
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
    entry initial (fun _ => initialV)

/-- Trap path 4 (L = 8) over ChainInv3 (trapOff 8) ∧ ValBindT 8 q, under TrapPath 8 pins q. -/
theorem trap4_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 8 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 8 pins q)
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : ValBindT 8 q 0 entry) :
    (∀ k, k ≤ 8 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 8 → ValBindT 8 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 8).regs._PC = base + trapOffset :=
  RtBl.TrapV.trap4_runV real spec config rows mapping base budget pins table static
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
    entry initial (fun _ => initialV)

/-- Trap path 5 (L = 10) over ChainInv3 (trapOff 10) ∧ ValBindT 10 q, under TrapPath 10 pins q. -/
theorem trap5_runT (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 10 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (q : Inputs) (np : TrapPath 10 pins q)
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : ValBindT 10 q 0 entry) :
    (∀ k, k ≤ 10 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        (k < 10 → ValBindT 10 q k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k))) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 10).regs._PC = base + trapOffset :=
  RtBl.TrapV.trap5_runV real spec config rows mapping base budget pins table static
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
    entry initial (fun _ => initialV)

#print axioms trap0_runT
#print axioms trap1_runT
#print axioms trap2_runT
#print axioms trap3_runT
#print axioms trap4_runT
#print axioms trap5_runT
end RtBl.TrapT
