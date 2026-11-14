-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapBranchStep
import DefaultBcondEventTail
import DefaultHeapCbzTail
import DefaultHeapCode
import HeapV2StepCerts.Residue.Step5Branch_01
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable

#check "CURRENT_DECL heap step_41"
theorem step_41 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 41 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 41 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 41 ≤ drawsBefore (41 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 41 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 41 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (41 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (41 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 41 (DefaultHeapBranchStep.BranchEffects spec mapping 41) []
    (fun x inv => by
      have dec := ValBind.dec_41 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (41 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 41 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 41 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_41 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 41 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_41

#check "CURRENT_DECL heap step_45"
theorem step_45 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 45 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 45 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 45 ≤ drawsBefore (45 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 45 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 45 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (45 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (45 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 45 (DefaultHeapBranchStep.BranchEffects spec mapping 45) []
    (fun x inv => by
      have dec := ValBind.dec_45 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (45 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 45 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 45 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_45 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 45 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_45

#check "CURRENT_DECL heap step_49"
theorem step_49 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 49 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 49 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 49 ≤ drawsBefore (49 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 49 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 49 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (49 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (49 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 49 (DefaultHeapBranchStep.BranchEffects spec mapping 49) []
    (fun x inv => by
      have dec := ValBind.dec_49 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (49 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 49 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 49 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_49 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 49 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_49

#check "CURRENT_DECL heap step_53"
theorem step_53 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 53 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 53 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 53 ≤ drawsBefore (53 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 53 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 53 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (53 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (53 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 53 (DefaultHeapBranchStep.BranchEffects spec mapping 53) []
    (fun x inv => by
      have dec := ValBind.dec_53 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (53 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 53 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 53 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_53 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 53 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_53

#check "CURRENT_DECL heap step_57"
theorem step_57 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 57 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 57 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 57 ≤ drawsBefore (57 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 57 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 57 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (57 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (57 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 57 (DefaultHeapBranchStep.BranchEffects spec mapping 57) []
    (fun x inv => by
      have dec := ValBind.dec_57 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (57 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 57 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 57 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_57 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 57 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_57

#check "CURRENT_DECL heap step_61"
theorem step_61 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 61 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 61 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 61 ≤ drawsBefore (61 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 61 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 61 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (61 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (61 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 61 (DefaultHeapBranchStep.BranchEffects spec mapping 61) []
    (fun x inv => by
      have dec := ValBind.dec_61 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (61 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 61 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 61 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_61 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 61 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_61

#check "CURRENT_DECL heap step_65"
theorem step_65 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 65 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 65 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 65 ≤ drawsBefore (65 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 65 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 65 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (65 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (65 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 65 (DefaultHeapBranchStep.BranchEffects spec mapping 65) []
    (fun x inv => by
      have dec := ValBind.dec_65 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (65 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 65 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 65 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_65 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 65 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_65

#check "CURRENT_DECL heap step_69"
theorem step_69 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 69 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 69 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 69 ≤ drawsBefore (69 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 69 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 69 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (69 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (69 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 69 (DefaultHeapBranchStep.BranchEffects spec mapping 69) []
    (fun x inv => by
      have dec := ValBind.dec_69 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (69 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 69 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 69 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_69 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 69 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_69

#check "CURRENT_DECL heap step_73"
theorem step_73 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 73 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 73 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 73 ≤ drawsBefore (73 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 73 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 73 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (73 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (73 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 73 (DefaultHeapBranchStep.BranchEffects spec mapping 73) []
    (fun x inv => by
      have dec := ValBind.dec_73 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (73 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 73 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 73 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_73 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 73 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_73

#check "CURRENT_DECL heap step_77"
theorem step_77 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 77 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 77 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 77 ≤ drawsBefore (77 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 77 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 77 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (77 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (77 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 77 (DefaultHeapBranchStep.BranchEffects spec mapping 77) []
    (fun x inv => by
      have dec := ValBind.dec_77 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (77 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 77 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 77 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_77 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 77 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_77

#check "CURRENT_DECL heap step_81"
theorem step_81 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 81 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 81 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 81 ≤ drawsBefore (81 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 81 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 81 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (81 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (81 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 81 (DefaultHeapBranchStep.BranchEffects spec mapping 81) []
    (fun x inv => by
      have dec := ValBind.dec_81 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (81 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 81 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 81 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_81 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 81 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_81

#check "CURRENT_DECL heap step_85"
theorem step_85 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 85 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 85 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 85 ≤ drawsBefore (85 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 85 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 85 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (85 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (85 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 85 (DefaultHeapBranchStep.BranchEffects spec mapping 85) []
    (fun x inv => by
      have dec := ValBind.dec_85 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (85 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 85 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 85 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_85 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 85 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_85

end ReleaseProfile.DefaultHeapBranchRows
