-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapBranchStep
import DefaultBcondEventTail
import DefaultHeapCbzTail
import DefaultHeapCode
import HeapV2StepCerts.Residue.Step5Branch_03
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable

#check "CURRENT_DECL heap step_137"
theorem step_137 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 137 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 137 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 137 ≤ drawsBefore (137 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 137 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 137 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (137 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (137 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 137 (DefaultHeapBranchStep.BranchEffects spec mapping 137) []
    (fun x inv => by
      have dec := ValBind.dec_137 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (137 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 137 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 137 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_137 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 137 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_137

#check "CURRENT_DECL heap step_141"
theorem step_141 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 141 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 141 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 141 ≤ drawsBefore (141 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 141 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 141 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (141 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (141 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 141 (DefaultHeapBranchStep.BranchEffects spec mapping 141) []
    (fun x inv => by
      have dec := ValBind.dec_141 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (141 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 141 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 141 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_141 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 141 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_141

#check "CURRENT_DECL heap step_145"
theorem step_145 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 145 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 145 + sign_extend (524285#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 145 ≤ drawsBefore (145 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 145 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 145 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (145 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (145 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 145 (DefaultHeapBranchStep.BranchEffects spec mapping 145) []
    (fun x inv => by
      have dec := ValBind.dec_145 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (145 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 145 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 145 pins table catalogue static 0x13c 0x54ffffa1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_145 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 145 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_145

#check "CURRENT_DECL heap step_151"
theorem step_151 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 151 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 151 + sign_extend (5#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 151 ≤ drawsBefore (151 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 151 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 151 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (151 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (151 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 151 (DefaultHeapBranchStep.BranchEffects spec mapping 151) []
    (fun x inv => by
      have dec := ValBind.dec_151 np inv.body.regBind inv.valBind
      have target : (if Crypto.CruxCbz.cbzC 1#1 2#5 x then x.regs._PC + sign_extend (5#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (151 + 1) := by
        rw [ite_eq_right (fun h => by cases dec.mp h), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (5#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 151 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (EntryBodyCbz.W 2#5 5#19) 118 (by decide) (by decide) x inv.body (DefaultHeapCbzTail.tail_at real x 2#5 5#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 151 pins table catalogue static 0x178 0xb40000a2
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_151 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 151 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_151

#check "CURRENT_DECL heap step_155"
theorem step_155 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 155 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 155 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 155 ≤ drawsBefore (155 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 155 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 155 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (155 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (155 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 155 (DefaultHeapBranchStep.BranchEffects spec mapping 155) []
    (fun x inv => by
      have dec := ValBind.dec_155 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (155 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 155 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 155 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_155 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 155 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_155

#check "CURRENT_DECL heap step_158"
theorem step_158 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 158 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 158 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 158 ≤ drawsBefore (158 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 158 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 158 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (158 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (158 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 158 (DefaultHeapBranchStep.BranchEffects spec mapping 158) []
    (fun x inv => by
      have dec := ValBind.dec_158 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (158 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 158 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 158 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_158 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 158 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_158

#check "CURRENT_DECL heap step_161"
theorem step_161 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 161 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 161 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 161 ≤ drawsBefore (161 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 161 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 161 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (161 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (161 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 161 (DefaultHeapBranchStep.BranchEffects spec mapping 161) []
    (fun x inv => by
      have dec := ValBind.dec_161 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (161 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 161 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 161 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_161 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 161 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_161

#check "CURRENT_DECL heap step_164"
theorem step_164 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 164 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 164 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 164 ≤ drawsBefore (164 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 164 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 164 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (164 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (164 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 164 (DefaultHeapBranchStep.BranchEffects spec mapping 164) []
    (fun x inv => by
      have dec := ValBind.dec_164 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (164 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 164 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 164 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_164 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 164 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_164

#check "CURRENT_DECL heap step_167"
theorem step_167 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 167 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 167 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 167 ≤ drawsBefore (167 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 167 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 167 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (167 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (167 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 167 (DefaultHeapBranchStep.BranchEffects spec mapping 167) []
    (fun x inv => by
      have dec := ValBind.dec_167 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (167 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 167 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 167 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_167 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 167 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_167

#check "CURRENT_DECL heap step_170"
theorem step_170 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 170 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 170 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 170 ≤ drawsBefore (170 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 170 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 170 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (170 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (170 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 170 (DefaultHeapBranchStep.BranchEffects spec mapping 170) []
    (fun x inv => by
      have dec := ValBind.dec_170 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (170 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 170 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 170 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_170 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 170 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_170

#check "CURRENT_DECL heap step_173"
theorem step_173 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 173 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 173 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 173 ≤ drawsBefore (173 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 173 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 173 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (173 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (173 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 173 (DefaultHeapBranchStep.BranchEffects spec mapping 173) []
    (fun x inv => by
      have dec := ValBind.dec_173 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (173 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 173 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 173 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_173 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 173 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_173

#check "CURRENT_DECL heap step_176"
theorem step_176 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 176 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 176 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 176 ≤ drawsBefore (176 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 176 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 176 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (176 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (176 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 176 (DefaultHeapBranchStep.BranchEffects spec mapping 176) []
    (fun x inv => by
      have dec := ValBind.dec_176 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (176 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 176 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 176 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_176 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 176 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_176

end ReleaseProfile.DefaultHeapBranchRows
