-- Current-profile heap branch rows with actual Sail successors and events.
import DefaultHeapResidue
import DefaultHeapBranchStep
import DefaultBcondEventTail
import DefaultHeapCbzTail
import DefaultHeapCode
import HeapV2StepCerts.Residue.Step5Branch_04
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxGenGuarded HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapBranchRows
open ReleaseProfile.DefaultHeapResidue
attribute [local instance 10] Classical.propDecidable

#check "CURRENT_DECL heap step_179"
theorem step_179 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 179 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 179 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 179 ≤ drawsBefore (179 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 179 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 179 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (179 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (179 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 179 (DefaultHeapBranchStep.BranchEffects spec mapping 179) []
    (fun x inv => by
      have dec := ValBind.dec_179 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (179 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 179 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 179 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_179 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 179 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_179

#check "CURRENT_DECL heap step_182"
theorem step_182 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 182 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 182 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 182 ≤ drawsBefore (182 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 182 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 182 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (182 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (182 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 182 (DefaultHeapBranchStep.BranchEffects spec mapping 182) []
    (fun x inv => by
      have dec := ValBind.dec_182 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (182 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 182 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 182 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_182 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 182 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_182

#check "CURRENT_DECL heap step_185"
theorem step_185 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 185 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 185 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 185 ≤ drawsBefore (185 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 185 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 185 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (185 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (185 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 185 (DefaultHeapBranchStep.BranchEffects spec mapping 185) []
    (fun x inv => by
      have dec := ValBind.dec_185 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (185 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 185 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 185 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_185 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 185 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_185

#check "CURRENT_DECL heap step_188"
theorem step_188 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 188 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 188 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 188 ≤ drawsBefore (188 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 188 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 188 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (188 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (188 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 188 (DefaultHeapBranchStep.BranchEffects spec mapping 188) []
    (fun x inv => by
      have dec := ValBind.dec_188 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (188 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 188 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 188 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_188 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 188 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_188

#check "CURRENT_DECL heap step_191"
theorem step_191 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 191 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 191 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 191 ≤ drawsBefore (191 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 191 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 191 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (191 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (191 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 191 (DefaultHeapBranchStep.BranchEffects spec mapping 191) []
    (fun x inv => by
      have dec := ValBind.dec_191 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (191 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 191 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 191 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_191 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 191 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_191

#check "CURRENT_DECL heap step_194"
theorem step_194 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 194 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 194 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 194 ≤ drawsBefore (194 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 194 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 194 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (194 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (194 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 194 (DefaultHeapBranchStep.BranchEffects spec mapping 194) []
    (fun x inv => by
      have dec := ValBind.dec_194 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (194 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 194 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 194 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_194 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 194 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_194

#check "CURRENT_DECL heap step_197"
theorem step_197 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 197 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 197 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 197 ≤ drawsBefore (197 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 197 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 197 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (197 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (197 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 197 (DefaultHeapBranchStep.BranchEffects spec mapping 197) []
    (fun x inv => by
      have dec := ValBind.dec_197 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (197 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 197 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 197 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_197 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 197 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_197

#check "CURRENT_DECL heap step_200"
theorem step_200 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 200 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 200 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 200 ≤ drawsBefore (200 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 200 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 200 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (200 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (200 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 200 (DefaultHeapBranchStep.BranchEffects spec mapping 200) []
    (fun x inv => by
      have dec := ValBind.dec_200 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (200 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 200 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 200 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_200 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 200 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_200

#check "CURRENT_DECL heap step_203"
theorem step_203 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 203 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 203 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 203 ≤ drawsBefore (203 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 203 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 203 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (203 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (203 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 203 (DefaultHeapBranchStep.BranchEffects spec mapping 203) []
    (fun x inv => by
      have dec := ValBind.dec_203 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (203 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 203 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 203 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_203 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 203 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_203

#check "CURRENT_DECL heap step_206"
theorem step_206 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 206 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 206 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 206 ≤ drawsBefore (206 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 206 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 206 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (206 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (206 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 206 (DefaultHeapBranchStep.BranchEffects spec mapping 206) []
    (fun x inv => by
      have dec := ValBind.dec_206 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (206 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 206 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 206 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_206 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 206 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_206

#check "CURRENT_DECL heap step_209"
theorem step_209 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 209 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 209 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 209 ≤ drawsBefore (209 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 209 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 209 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (209 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (209 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 209 (DefaultHeapBranchStep.BranchEffects spec mapping 209) []
    (fun x inv => by
      have dec := ValBind.dec_209 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (209 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 209 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 209 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_209 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 209 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_209

#check "CURRENT_DECL heap step_212"
theorem step_212 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 212 < budget) (page : base.toNat % 4096 = 0)
    (lowT : (base + (HeapV2Compose.offsetOf 212 + sign_extend (524286#19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (q : HeapV2StepCerts.ValBind.Inputs) (np : HeapV2StepCerts.ValBind.NormalPath pins q) (v19 v30 : BitVec 64) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (drawsNext : drawsBefore 212 ≤ drawsBefore (212 + 1)) :
    Step real spec mapping []
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 212 x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry 212 x)
      (fun x => Inv spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 (212 + 1) x ∧ HeapV2StepCerts.Residue.ResL pins mapping base v19 v30 entry (212 + 1) x) := by
  exact step_of_at real spec config rows mapping _ codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins catalogue entry capacity drawsBefore q v19 v30 212 (DefaultHeapBranchStep.BranchEffects spec mapping 212) []
    (fun x inv => by
      have dec := ValBind.dec_212 np inv.body.regBind inv.valBind
      have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
        else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (212 + 1) := by
        rw [ite_eq_left (dec.mpr rfl), inv.body.core.v1.pc, BitVec.add_assoc]
        congr 1 <;> decide
      have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
        rw [inv.body.core.v1.pc, BitVec.add_assoc]
        exact lowT
      exact DefaultHeapBranchStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
        static.separated base HeapV2Compose.offsetOf budget pins 212 catalogue entry capacity drawsBefore drawsNext room (by decide) page (by decide)
        (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) nodup
        (DefaultHeapCode.memFetch spec config rows mapping base budget 212 pins table catalogue static 0x188 0x54ffffc1
          (by decide) (by decide) _ (by decide) x inv.body.core))
    (fun _ _ rb vb r => HeapV2StepCerts.ValBind.carry_212 np rb vb r.holds r.value)
    (fun _ _ r field => RtSaved2.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr field)
    (fun _ _ r => r.gcs) entry
    (fun _ _ r res => ⟨HeapV2StepCerts.Residue.res_eq (HeapV2StepCerts.Residue.frameKeep_ok 212 (by decide)) r.holds r.mem res.1, RtSaved3.carry_branch (by decide) (by decide) (by decide) (by decide) r.mem r.gpr res.2⟩)
    (fun _ _ r => r.z) (fun _ _ r => r.events)

#print axioms step_212

end ReleaseProfile.DefaultHeapBranchRows
