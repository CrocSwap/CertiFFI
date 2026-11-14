-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import DefaultHeapDitStep
import DefaultHeapBranchRows03
import DefaultHeapBranchRows04
import DefaultHeapBranchRowsCall
import DefaultHeapClassRows02
import DefaultHeapMemDitRows03
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun
open ReleaseProfile
open ReleaseProfile.DefaultHeapResidue (controls)
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap dit_segment_05"
theorem dit_segment_05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 150 ≤ k → k < 180 → ∀ x, RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro k lo hi x inv
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have target : NativeEntryCallerParts.blTarget 75#26 x = base + HeapV2Compose.offsetOf (150 + 1) := by
      rw [NativeEntryCallerRegisters.bl_target, inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    exact DefaultHeapDitStep.bl real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 150 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      75#26 (by decide) (by decide) x inv.1.body (by rw [target]; exact (low_of _ (by decide) dp.low)) (controls inv.1) target dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 150 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 76 2483028043
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_151 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.CruxCbz.cbzC 1#1 2#5 x then x.regs._PC + sign_extend (5#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (151 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (5#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 151 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (EntryBodyCbz.W 2#5 5#19) 118 (by decide) (by decide) x inv.1.body (DefaultHeapCbzTail.tail_at real x 2#5 5#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 151 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x178 0xb40000a2
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 152 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_152 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 152 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x17c 0xaa0003e3
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 152 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x17c 0xaa0003e3
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_153 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_153] using dp.rowsRoom 153 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_153] using dp.rowsNext 153 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 154 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_154 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 154 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 154 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_155 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (155 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 155 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 155 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_156 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_156] using dp.rowsRoom 156 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_156] using dp.rowsNext 156 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 157 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_157 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 157 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 157 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_158 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (158 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 158 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 158 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_159 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_159] using dp.rowsRoom 159 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_159] using dp.rowsNext 159 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 160 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_160 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 160 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 160 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_161 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (161 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 161 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 161 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_162 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_162] using dp.rowsRoom 162 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_162] using dp.rowsNext 162 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 163 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_163 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 163 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 163 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_164 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (164 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 164 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 164 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_165 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_165] using dp.rowsRoom 165 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_165] using dp.rowsNext 165 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 166 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_166 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 166 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 166 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_167 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (167 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 167 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 167 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_168 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_168] using dp.rowsRoom 168 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_168] using dp.rowsNext 168 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 169 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_169 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 169 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 169 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_170 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (170 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 170 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 170 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_171 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_171] using dp.rowsRoom 171 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_171] using dp.rowsNext 171 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 172 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_172 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 172 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 172 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_173 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (173 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 173 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 173 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_174 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_174] using dp.rowsRoom 174 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_174] using dp.rowsNext 174 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 175 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_175 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 175 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 175 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_176 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (176 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 176 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 176 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_177 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_177] using dp.rowsRoom 177 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_177] using dp.rowsNext 177 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 178 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_178 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 178 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 178 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_179 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (179 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 179 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 179 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  omega
#print axioms dit_segment_05
end ReleaseProfile.DefaultHeapRun
