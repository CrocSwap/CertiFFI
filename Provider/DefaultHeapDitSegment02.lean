-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import DefaultHeapDitStep
import DefaultHeapBranchRows01
import DefaultHeapBranchRows02
import DefaultHeapClassRows00
import DefaultHeapClassRows01
import DefaultHeapMemDitRows01
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


#check "CURRENT_DECL heap dit_segment_02"
theorem dit_segment_02 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 60 ≤ k → k < 90 → ∀ x, RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro k lo hi x inv
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 60 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_60 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 60 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 60 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_61 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (61 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 61 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 61 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_62 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_62] using dp.rowsRoom 62 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_62] using dp.rowsNext 62 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_63 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_63] using dp.rowsRoom 63 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_63] using dp.rowsNext 63 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 64 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_64 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 64 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 64 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_65 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (65 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 65 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 65 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_66 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_66] using dp.rowsRoom 66 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_66] using dp.rowsNext 66 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_67 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_67] using dp.rowsRoom 67 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_67] using dp.rowsNext 67 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 68 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_68 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 68 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 68 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_69 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (69 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 69 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 69 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_70 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_70] using dp.rowsRoom 70 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_70] using dp.rowsNext 70 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_71 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_71] using dp.rowsRoom 71 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_71] using dp.rowsNext 71 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 72 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_72 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 72 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 72 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_73 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (73 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 73 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 73 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_74 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_74] using dp.rowsRoom 74 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_74] using dp.rowsNext 74 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_75 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_75] using dp.rowsRoom 75 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_75] using dp.rowsNext 75 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 76 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_76 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 76 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 76 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_77 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (77 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 77 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 77 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_78 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_78] using dp.rowsRoom 78 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_78] using dp.rowsNext 78 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_79 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_79] using dp.rowsRoom 79 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_79] using dp.rowsNext 79 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 80 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_80 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 80 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 80 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_81 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (81 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 81 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 81 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_82 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_82] using dp.rowsRoom 82 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_82] using dp.rowsNext 82 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_83 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_83] using dp.rowsRoom 83 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_83] using dp.rowsNext 83 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 84 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_84 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 84 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 84 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_85 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (85 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 85 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 85 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_86 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_86] using dp.rowsRoom 86 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_86] using dp.rowsNext 86 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_87 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_87] using dp.rowsRoom 87 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_87] using dp.rowsNext 87 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 88 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_88 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 88 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 88 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_89 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (89 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 89 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 89 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  omega
#print axioms dit_segment_02
end ReleaseProfile.DefaultHeapRun
