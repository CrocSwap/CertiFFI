-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import DefaultHeapValueBranch
import ArmCertValue.HP1Run
import ArmCertValue.Glue
import DefaultHeapBranchRowsCall
import DefaultHeapBranchRows00
import DefaultHeapBranchRows01
import DefaultHeapBranchRows02
import DefaultHeapBranchRows03
import DefaultHeapBranchRows04
import DefaultHeapBranchRows05
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun
attribute [local instance 10] Classical.propDecidable

theorem value_branch_0 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 0
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_0 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.CruxCbz.cbzC 1#1 0#5 x then x.regs._PC + sign_extend (179#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (0 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (179#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 0 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (EntryBodyCbz.W 0#5 179#19) 118 (by decide) (by decide) x inv.1.body (DefaultHeapCbzTail.tail_at real x 0#5 179#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 0 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x0 0xb4001660
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_0

theorem value_branch_1 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 1
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_1 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.CruxCbz.cbzC 1#1 1#5 x then x.regs._PC + sign_extend (178#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (1 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (178#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 1 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (EntryBodyCbz.W 1#5 178#19) 118 (by decide) (by decide) x inv.1.body (DefaultHeapCbzTail.tail_at real x 1#5 178#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 1 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x4 0xb4001641
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_1

theorem value_branch_3 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 3
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_3 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (176#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (3 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (176#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 3 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 176#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 176#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 3 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0xc 0x54001601
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_3

theorem value_branch_5 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 5
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_5 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (174#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (5 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (174#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 5 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 174#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 174#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 5 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x14 0x540015c1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_5

theorem value_branch_7 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 7
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_7 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 3#4 x.regs then x.regs._PC + sign_extend (172#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (7 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (172#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 7 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 3#4 172#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 3#4 172#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 7 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1c 0x54001583
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_7

theorem value_branch_9 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 9
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_9 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (170#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (9 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (170#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 9 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 170#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 170#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 9 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x24 0x54001541
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_9

theorem value_branch_16 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 16
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_16 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.CruxCbz.cbzC 1#1 2#5 x then x.regs._PC + sign_extend (6#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (16 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (6#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 16 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (EntryBodyCbz.W 2#5 6#19) 118 (by decide) (by decide) x inv.1.body (DefaultHeapCbzTail.tail_at real x 2#5 6#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 16 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x128 0xb40000c2
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_16

theorem value_branch_21 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 21
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_21 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (21 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 21 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 21 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_21

theorem value_branch_25 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 25
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_25 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (25 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 25 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 25 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_25

theorem value_branch_29 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 29
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_29 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (29 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 29 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 29 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_29

theorem value_branch_33 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 33
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_33 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (33 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 33 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 33 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_33

theorem value_branch_37 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 37
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_37 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (37 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 37 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 37 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_37

theorem value_branch_41 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 41
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_41 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (41 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 41 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 41 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_41

theorem value_branch_45 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 45
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_45 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (45 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 45 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 45 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_45

theorem value_branch_49 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 49
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_49 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (49 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 49 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 49 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_49

theorem value_branch_53 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 53
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_53 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (53 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 53 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 53 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_53

theorem value_branch_57 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 57
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_57 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (57 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 57 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 57 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_57

theorem value_branch_61 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 61
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_61 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (61 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 61 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 61 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_61

theorem value_branch_65 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 65
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_65 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (65 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 65 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 65 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_65

theorem value_branch_69 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 69
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_69 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (69 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 69 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 69 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_69

theorem value_branch_73 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 73
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_73 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (73 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 73 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 73 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_73

theorem value_branch_77 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 77
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_77 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (77 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 77 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 77 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_77

theorem value_branch_81 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 81
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_81 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (81 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 81 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 81 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_81

theorem value_branch_85 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 85
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_85 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (85 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 85 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 85 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_85

theorem value_branch_89 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 89
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_89 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (89 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 89 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 89 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_89

theorem value_branch_93 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 93
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_93 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (93 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 93 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 93 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_93

theorem value_branch_97 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 97
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_97 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (97 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 97 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 97 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_97

theorem value_branch_101 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 101
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_101 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (101 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 101 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 101 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_101

theorem value_branch_105 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 105
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_105 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (105 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 105 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 105 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_105

theorem value_branch_109 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 109
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_109 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (109 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 109 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 109 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_109

theorem value_branch_113 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 113
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_113 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (113 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 113 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 113 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_113

theorem value_branch_117 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 117
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_117 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (117 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 117 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 117 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_117

theorem value_branch_121 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 121
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_121 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (121 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 121 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 121 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_121

theorem value_branch_125 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 125
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_125 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (125 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 125 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 125 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_125

theorem value_branch_129 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 129
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_129 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (129 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 129 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 129 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_129

theorem value_branch_133 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 133
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_133 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (133 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 133 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 133 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_133

theorem value_branch_137 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 137
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_137 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (137 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 137 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 137 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_137

theorem value_branch_141 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 141
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_141 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (141 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 141 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 141 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_141

theorem value_branch_145 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 145
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_145 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (145 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 145 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 145 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_145

theorem value_branch_146 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 146
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 146 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (EntryBodyRet.W 30#5) 94 (by decide) (by decide) x inv.1.body (DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) (by rw [RtSaved2.link_target (by decide) inv.1.lr]; exact (low_of _ (by decide) dp.low)) _ (RtSaved2.link_target (by decide) inv.1.lr)) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 146 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x140 0xd65f03c0
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_146

theorem value_branch_151 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 151
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_151 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.CruxCbz.cbzC 1#1 2#5 x then x.regs._PC + sign_extend (5#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (151 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (5#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 151 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (EntryBodyCbz.W 2#5 5#19) 118 (by decide) (by decide) x inv.1.body (DefaultHeapCbzTail.tail_at real x 2#5 5#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 151 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x178 0xb40000a2
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_151

theorem value_branch_155 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 155
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_155 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (155 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 155 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 155 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_155

theorem value_branch_158 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 158
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_158 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (158 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 158 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 158 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_158

theorem value_branch_161 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 161
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_161 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (161 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 161 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 161 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_161

theorem value_branch_164 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 164
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_164 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (164 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 164 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 164 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_164

theorem value_branch_167 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 167
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_167 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (167 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 167 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 167 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_167

theorem value_branch_170 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 170
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_170 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (170 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 170 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 170 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_170

theorem value_branch_173 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 173
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_173 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (173 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 173 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 173 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_173

theorem value_branch_176 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 176
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_176 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (176 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 176 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 176 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_176

theorem value_branch_179 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 179
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_179 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (179 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 179 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 179 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_179

theorem value_branch_182 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 182
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_182 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (182 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 182 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 182 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_182

theorem value_branch_185 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 185
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_185 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (185 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 185 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 185 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_185

theorem value_branch_188 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 188
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_188 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (188 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 188 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 188 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_188

theorem value_branch_191 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 191
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_191 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (191 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 191 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 191 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_191

theorem value_branch_194 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 194
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_194 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (194 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 194 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 194 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_194

theorem value_branch_197 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 197
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_197 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (197 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 197 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 197 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_197

theorem value_branch_200 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 200
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_200 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (200 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 200 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 200 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_200

theorem value_branch_203 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 203
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_203 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (203 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 203 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 203 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_203

theorem value_branch_206 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 206
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_206 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (206 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 206 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 206 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_206

theorem value_branch_209 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 209
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_209 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (209 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 209 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 209 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_209

theorem value_branch_212 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 212
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_212 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (212 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 212 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 212 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_212

theorem value_branch_215 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 215
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_215 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (215 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 215 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 215 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_215

theorem value_branch_218 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 218
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_218 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (218 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 218 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 218 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_218

theorem value_branch_221 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 221
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_221 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (221 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 221 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 221 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_221

theorem value_branch_224 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 224
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_224 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (224 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 224 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 224 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_224

theorem value_branch_227 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 227
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_227 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (227 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 227 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 227 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_227

theorem value_branch_230 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 230
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_230 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (230 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 230 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 230 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_230

theorem value_branch_233 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 233
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_233 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (233 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 233 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 233 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_233

theorem value_branch_236 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 236
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_236 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (236 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 236 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 236 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_236

theorem value_branch_239 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 239
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_239 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (239 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 239 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 239 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_239

theorem value_branch_242 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 242
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_242 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (242 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 242 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 242 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_242

theorem value_branch_245 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 245
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_245 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (245 + 1) := by
    rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 245 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 245 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_245

theorem value_branch_248 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 248
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  have dec := ValBind.dec_248 dp.np inv.1.body.regBind inv.1.valBind
  have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
    else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (248 + 1) := by
    rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
    congr 1 <;> decide
  have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
    exact (low_of _ (by decide) dp.low)
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 248 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 248 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_248

theorem value_branch_249 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 249
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 249 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (EntryBodyRet.W 30#5) 94 (by decide) (by decide) x inv.1.body (DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) (by rw [RtSaved2.link_target (by decide) inv.1.lr]; exact (low_of _ (by decide) dp.low)) _ (RtSaved2.link_target (by decide) inv.1.lr)) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 249 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x18c 0xd65f03c0
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_249

theorem value_branch_331 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ArmCertValue.StepFact real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) mapping (HeapV2E17.pin pins)
      ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan 331
      (by rw [ArmCertValue.HeapV2Plan.plan_length]; decide) := by
  intro x inv
  obtain ⟨fin, run, vh, mem⟩ := DefaultHeapValueBranch.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
    dp.static.separated base HeapV2Compose.offsetOf budget pins 331 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
    (EntryBodyRet.W 30#5) 94 (by decide) (by decide) x inv.1.body (DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) (by rw [RtSaved2.link_target (by decide) inv.1.lr]; exact (low_of _ (by decide) dp.low)) _ (RtSaved2.link_target (by decide) inv.1.lr)) dp.nodup
    (DefaultHeapCode.memFetch spec config rows mapping base budget 331 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x2c8 0xd65f03c0
      (by decide) (by decide) _ (by decide) x inv.1.body.core)
  exact ⟨fin, run, vh, ArmBridge.CruxGenGuarded.ChainInvV4X.memV_nil_of_mem _ _ _ _ _ mem⟩
#print axioms value_branch_331

end ReleaseProfile.DefaultHeapRun
