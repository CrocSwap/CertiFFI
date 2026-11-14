-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import DefaultHeapDitStep
import DefaultHeapBranchRows00
import DefaultHeapBranchRowsCall
import DefaultHeapClassRows00
import DefaultHeapMemDitRows00
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


#check "CURRENT_DECL heap dit_segment_00"
theorem dit_segment_00 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 0 ≤ k → k < 30 → ∀ x, RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro k lo hi x inv
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_0 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.CruxCbz.cbzC 1#1 0#5 x then x.regs._PC + sign_extend (179#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (0 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (179#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 0 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (EntryBodyCbz.W 0#5 179#19) 118 (by decide) (by decide) x inv.1.body (DefaultHeapCbzTail.tail_at real x 0#5 179#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 0 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x0 0xb4001660
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_1 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.CruxCbz.cbzC 1#1 1#5 x then x.regs._PC + sign_extend (178#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (1 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (178#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 1 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (EntryBodyCbz.W 1#5 178#19) 118 (by decide) (by decide) x inv.1.body (DefaultHeapCbzTail.tail_at real x 1#5 178#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 1 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x4 0xb4001641
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 2 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_2 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 2 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x8 0xf240081f
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 2 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x8 0xf240081f
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_3 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (176#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (3 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (176#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 3 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 176#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 176#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 3 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0xc 0x54001601
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 4 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_4 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 4 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x10 0xf240083f
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 4 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x10 0xf240083f
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_5 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (174#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (5 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (174#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 5 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 174#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 174#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 5 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x14 0x540015c1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 6 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_6 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 6 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x18 0xf100805f
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 6 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x18 0xf100805f
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_7 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 3#4 x.regs then x.regs._PC + sign_extend (172#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (7 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (172#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 7 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 3#4 172#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 3#4 172#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 7 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1c 0x54001583
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 8 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_8 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 8 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x20 0xf100807f
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 8 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x20 0xf100807f
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_9 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (170#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (9 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (170#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 9 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 170#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 170#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 9 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x24 0x54001541
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 10 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_10 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 10 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x28 0xd10103ff
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 10 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x28 0xd10103ff
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_11 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_11] using dp.rowsRoom 11 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_11] using dp.rowsNext 11 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 12 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_12 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 12 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x30 0xaa0003f3
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 12 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x30 0xaa0003f3
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 13 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_13 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 13 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x34 0x910003e0
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 13 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x34 0x910003e0
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 14 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_14 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 14 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x38 0xd2800402
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 14 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x38 0xd2800402
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have target : NativeEntryCallerParts.blTarget 59#26 x = base + HeapV2Compose.offsetOf (15 + 1) := by
      rw [NativeEntryCallerRegisters.bl_target, inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    exact DefaultHeapDitStep.bl real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 15 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      59#26 (by decide) (by decide) x inv.1.body (by rw [target]; exact (low_of _ (by decide) dp.low)) (controls inv.1) target dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 15 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 60 2483028027
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_16 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.CruxCbz.cbzC 1#1 2#5 x then x.regs._PC + sign_extend (6#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (16 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (6#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 16 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (EntryBodyCbz.W 2#5 6#19) 118 (by decide) (by decide) x inv.1.body (DefaultHeapCbzTail.tail_at real x 2#5 6#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 16 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x128 0xb40000c2
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 17 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_17 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 17 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x12c 0xaa0003e3
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 17 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x12c 0xaa0003e3
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_18 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_18] using dp.rowsRoom 18 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_18] using dp.rowsNext 18 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_19 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_19] using dp.rowsRoom 19 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_19] using dp.rowsNext 19 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 20 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_20 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 20 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 20 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_21 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (21 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 21 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 21 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_22 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_22] using dp.rowsRoom 22 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_22] using dp.rowsNext 22 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_23 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_23] using dp.rowsRoom 23 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_23] using dp.rowsNext 23 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 24 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_24 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 24 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 24 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_25 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (25 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 25 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 25 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_26 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_26] using dp.rowsRoom 26 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_26] using dp.rowsNext 26 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_27 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_27] using dp.rowsRoom 27 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_27] using dp.rowsNext 27 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 28 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_28 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 28 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 28 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x138 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_29 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524285#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (29 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524285#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 29 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524285#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524285#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 29 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x13c 0x54ffffa1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  omega
#print axioms dit_segment_00
end ReleaseProfile.DefaultHeapRun
