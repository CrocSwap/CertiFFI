-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapBranchStep
import DefaultBcondEventTail
import DefaultHeapCbzTail
import DefaultHeapCode
import HeapV2StepCerts.Residue.Step5Branch_00
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable

#check "CURRENT_DECL heap step_0"
theorem step_0 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 0 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 0 ≤ drawsBefore (0 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 0 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 0 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (0 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (0 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 0 (DefaultHeapBranchStep.BranchEffects spec mapping 0) []
    (fun x inv => by
      have dec := ValBind.dec_0 np inv.body.regBind inv.valBind
      have target : (if Crypto.CruxCbz.cbzC 1#1 0#5 x then x.regs._PC + sign_extend (179#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (0 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (179#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 0 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (EntryBodyCbz.W 0#5 179#19) 118 (by decide) (by decide) x inv.body (DefaultHeapCbzTail.tail_at real x 0#5 179#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 0 pins table catalogue static 0x0 0xb4001660
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_0 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 0 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_0

#check "CURRENT_DECL heap step_1"
theorem step_1 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 1 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 1 ≤ drawsBefore (1 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 1 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 1 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (1 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (1 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 1 (DefaultHeapBranchStep.BranchEffects spec mapping 1) []
    (fun x inv => by
      have dec := ValBind.dec_1 np inv.body.regBind inv.valBind
      have target : (if Crypto.CruxCbz.cbzC 1#1 1#5 x then x.regs._PC + sign_extend (178#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (1 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (178#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 1 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (EntryBodyCbz.W 1#5 178#19) 118 (by decide) (by decide) x inv.body (DefaultHeapCbzTail.tail_at real x 1#5 178#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 1 pins table catalogue static 0x4 0xb4001641
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_1 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 1 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_1

#check "CURRENT_DECL heap step_3"
theorem step_3 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 3 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 3 ≤ drawsBefore (3 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 3 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 3 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (3 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (3 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 3 (DefaultHeapBranchStep.BranchEffects spec mapping 3) []
    (fun x inv => by
      have dec := ValBind.dec_3 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (176#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (3 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (176#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 3 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 176#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 176#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 3 pins table catalogue static 0xc 0x54001601
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_3 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 3 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_3

#check "CURRENT_DECL heap step_5"
theorem step_5 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 5 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 5 ≤ drawsBefore (5 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 5 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 5 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (5 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (5 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 5 (DefaultHeapBranchStep.BranchEffects spec mapping 5) []
    (fun x inv => by
      have dec := ValBind.dec_5 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (174#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (5 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (174#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 5 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 174#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 174#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 5 pins table catalogue static 0x14 0x540015c1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_5 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 5 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_5

#check "CURRENT_DECL heap step_7"
theorem step_7 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 7 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 7 + sign_extend (172#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 7 ≤ drawsBefore (7 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 7 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 7 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (7 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (7 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 7 (DefaultHeapBranchStep.BranchEffects spec mapping 7) []
    (fun x inv => by
      have dec := ValBind.dec_7 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 3#4 x.regs then x.regs._PC + sign_extend (172#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (7 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (172#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 7 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 3#4 172#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 3#4 172#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 7 pins table catalogue static 0x1c 0x54001583
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_7 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 7 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_7

#check "CURRENT_DECL heap step_9"
theorem step_9 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 9 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 9 + sign_extend (170#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 9 ≤ drawsBefore (9 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 9 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 9 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (9 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (9 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 9 (DefaultHeapBranchStep.BranchEffects spec mapping 9) []
    (fun x inv => by
      have dec := ValBind.dec_9 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (170#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (9 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (170#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 9 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 170#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 170#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 9 pins table catalogue static 0x24 0x54001541
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_9 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 9 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_9

#check "CURRENT_DECL heap step_16"
theorem step_16 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 16 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 16 + sign_extend (6#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 16 ≤ drawsBefore (16 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 16 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 16 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (16 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (16 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 16 (DefaultHeapBranchStep.BranchEffects spec mapping 16) []
    (fun x inv => by
      have dec := ValBind.dec_16 np inv.body.regBind inv.valBind
      have target : (if Crypto.CruxCbz.cbzC 1#1 2#5 x then x.regs._PC + sign_extend (6#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (16 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (6#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 16 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (EntryBodyCbz.W 2#5 6#19) 118 (by decide) (by decide) x inv.body (DefaultHeapCbzTail.tail_at real x 2#5 6#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 16 pins table catalogue static 0x128 0xb40000c2
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_16 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 16 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_16

#check "CURRENT_DECL heap step_21"
theorem step_21 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 21 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 21 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 21 ≤ drawsBefore (21 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 21 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 21 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (21 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (21 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 21 (DefaultHeapBranchStep.BranchEffects spec mapping 21) []
    (fun x inv => by
      have dec := ValBind.dec_21 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (21 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 21 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 21 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_21 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 21 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_21

#check "CURRENT_DECL heap step_25"
theorem step_25 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 25 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 25 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 25 ≤ drawsBefore (25 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 25 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 25 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (25 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (25 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 25 (DefaultHeapBranchStep.BranchEffects spec mapping 25) []
    (fun x inv => by
      have dec := ValBind.dec_25 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (25 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 25 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 25 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_25 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 25 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_25

#check "CURRENT_DECL heap step_29"
theorem step_29 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 29 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 29 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 29 ≤ drawsBefore (29 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 29 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 29 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (29 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (29 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 29 (DefaultHeapBranchStep.BranchEffects spec mapping 29) []
    (fun x inv => by
      have dec := ValBind.dec_29 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (29 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 29 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 29 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_29 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 29 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_29

#check "CURRENT_DECL heap step_33"
theorem step_33 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 33 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 33 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 33 ≤ drawsBefore (33 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 33 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 33 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (33 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (33 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 33 (DefaultHeapBranchStep.BranchEffects spec mapping 33) []
    (fun x inv => by
      have dec := ValBind.dec_33 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (33 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 33 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 33 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_33 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 33 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_33

#check "CURRENT_DECL heap step_37"
theorem step_37 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 37 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 37 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 37 ≤ drawsBefore (37 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 37 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 37 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (37 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (37 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 37 (DefaultHeapBranchStep.BranchEffects spec mapping 37) []
    (fun x inv => by
      have dec := ValBind.dec_37 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (37 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 37 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 37 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_37 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 37 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_37

end ReleaseProfile.DefaultHeapBranchRows
