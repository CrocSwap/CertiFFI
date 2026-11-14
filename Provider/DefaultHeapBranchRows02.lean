-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapBranchStep
import DefaultBcondEventTail
import DefaultHeapCbzTail
import DefaultHeapCode
import HeapV2StepCerts.Residue.Step5Branch_02
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable

#check "CURRENT_DECL heap step_89"
theorem step_89 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 89 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 89 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 89 ≤ drawsBefore (89 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 89 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 89 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (89 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (89 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 89 (DefaultHeapBranchStep.BranchEffects spec mapping 89) []
    (fun x inv => by
      have dec := ValBind.dec_89 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (89 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 89 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 89 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_89 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 89 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_89

#check "CURRENT_DECL heap step_93"
theorem step_93 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 93 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 93 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 93 ≤ drawsBefore (93 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 93 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 93 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (93 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (93 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 93 (DefaultHeapBranchStep.BranchEffects spec mapping 93) []
    (fun x inv => by
      have dec := ValBind.dec_93 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (93 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 93 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 93 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_93 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 93 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_93

#check "CURRENT_DECL heap step_97"
theorem step_97 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 97 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 97 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 97 ≤ drawsBefore (97 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 97 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 97 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (97 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (97 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 97 (DefaultHeapBranchStep.BranchEffects spec mapping 97) []
    (fun x inv => by
      have dec := ValBind.dec_97 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (97 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 97 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 97 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_97 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 97 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_97

#check "CURRENT_DECL heap step_101"
theorem step_101 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 101 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 101 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 101 ≤ drawsBefore (101 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 101 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 101 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (101 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (101 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 101 (DefaultHeapBranchStep.BranchEffects spec mapping 101) []
    (fun x inv => by
      have dec := ValBind.dec_101 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (101 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 101 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 101 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_101 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 101 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_101

#check "CURRENT_DECL heap step_105"
theorem step_105 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 105 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 105 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 105 ≤ drawsBefore (105 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 105 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 105 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (105 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (105 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 105 (DefaultHeapBranchStep.BranchEffects spec mapping 105) []
    (fun x inv => by
      have dec := ValBind.dec_105 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (105 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 105 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 105 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_105 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 105 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_105

#check "CURRENT_DECL heap step_109"
theorem step_109 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 109 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 109 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 109 ≤ drawsBefore (109 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 109 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 109 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (109 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (109 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 109 (DefaultHeapBranchStep.BranchEffects spec mapping 109) []
    (fun x inv => by
      have dec := ValBind.dec_109 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (109 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 109 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 109 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_109 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 109 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_109

#check "CURRENT_DECL heap step_113"
theorem step_113 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 113 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 113 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 113 ≤ drawsBefore (113 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 113 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 113 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (113 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (113 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 113 (DefaultHeapBranchStep.BranchEffects spec mapping 113) []
    (fun x inv => by
      have dec := ValBind.dec_113 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (113 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 113 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 113 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_113 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 113 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_113

#check "CURRENT_DECL heap step_117"
theorem step_117 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 117 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 117 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 117 ≤ drawsBefore (117 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 117 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 117 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (117 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (117 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 117 (DefaultHeapBranchStep.BranchEffects spec mapping 117) []
    (fun x inv => by
      have dec := ValBind.dec_117 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (117 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 117 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 117 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_117 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 117 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_117

#check "CURRENT_DECL heap step_121"
theorem step_121 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 121 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 121 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 121 ≤ drawsBefore (121 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 121 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 121 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (121 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (121 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 121 (DefaultHeapBranchStep.BranchEffects spec mapping 121) []
    (fun x inv => by
      have dec := ValBind.dec_121 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (121 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 121 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 121 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_121 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 121 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_121

#check "CURRENT_DECL heap step_125"
theorem step_125 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 125 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 125 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 125 ≤ drawsBefore (125 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 125 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 125 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (125 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (125 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 125 (DefaultHeapBranchStep.BranchEffects spec mapping 125) []
    (fun x inv => by
      have dec := ValBind.dec_125 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (125 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 125 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 125 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_125 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 125 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_125

#check "CURRENT_DECL heap step_129"
theorem step_129 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 129 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 129 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 129 ≤ drawsBefore (129 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 129 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 129 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (129 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (129 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 129 (DefaultHeapBranchStep.BranchEffects spec mapping 129) []
    (fun x inv => by
      have dec := ValBind.dec_129 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (129 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 129 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 129 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_129 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 129 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_129

#check "CURRENT_DECL heap step_133"
theorem step_133 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 133 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 133 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 133 ≤ drawsBefore (133 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 133 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 133 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (133 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (133 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 133 (DefaultHeapBranchStep.BranchEffects spec mapping 133) []
    (fun x inv => by
      have dec := ValBind.dec_133 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (133 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 133 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 133 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_133 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 133 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_133

end ReleaseProfile.DefaultHeapBranchRows
