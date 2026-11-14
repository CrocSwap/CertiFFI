-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import DefaultHeapDitStep
import DefaultHeapBranchRows04
import DefaultHeapBranchRows05
import DefaultHeapClassRows03
import DefaultHeapMemDitRows04
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


#check "CURRENT_DECL heap dit_segment_07"
theorem dit_segment_07 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 210 ≤ k → k < 240 → ∀ x, RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro k lo hi x inv
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_210 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_210] using dp.rowsRoom 210 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_210] using dp.rowsNext 210 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 211 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_211 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 211 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 211 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_212 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (212 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 212 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 212 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_213 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_213] using dp.rowsRoom 213 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_213] using dp.rowsNext 213 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 214 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_214 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 214 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 214 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_215 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (215 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 215 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 215 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_216 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_216] using dp.rowsRoom 216 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_216] using dp.rowsNext 216 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 217 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_217 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 217 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 217 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_218 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (218 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 218 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 218 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_219 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_219] using dp.rowsRoom 219 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_219] using dp.rowsNext 219 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 220 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_220 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 220 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 220 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_221 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (221 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 221 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 221 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_222 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_222] using dp.rowsRoom 222 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_222] using dp.rowsNext 222 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 223 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_223 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 223 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 223 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_224 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (224 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 224 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 224 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_225 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_225] using dp.rowsRoom 225 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_225] using dp.rowsNext 225 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 226 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_226 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 226 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 226 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_227 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (227 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 227 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 227 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_228 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_228] using dp.rowsRoom 228 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_228] using dp.rowsNext 228 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 229 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_229 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 229 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 229 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_230 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (230 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 230 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 230 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_231 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_231] using dp.rowsRoom 231 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_231] using dp.rowsNext 231 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 232 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_232 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 232 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 232 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_233 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (233 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 233 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 233 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_234 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_234] using dp.rowsRoom 234 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_234] using dp.rowsNext 234 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 235 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_235 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 235 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 235 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_236 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (236 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 236 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 236 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_237 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_237] using dp.rowsRoom 237 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_237] using dp.rowsNext 237 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 238 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_238 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 238 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 238 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_239 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (239 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 239 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 239 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  omega
#print axioms dit_segment_07
end ReleaseProfile.DefaultHeapRun
