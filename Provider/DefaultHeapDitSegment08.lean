-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import DefaultHeapDitStep
import DefaultHeapBranchRows05
import DefaultHeapBranchRowsCall
import DefaultHeapClassRows03
import DefaultHeapClassRows04
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


#check "CURRENT_DECL heap dit_segment_08"
theorem dit_segment_08 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 240 ≤ k → k < 270 → ∀ x, RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro k lo hi x inv
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_240 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_240] using dp.rowsRoom 240 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_240] using dp.rowsNext 240 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 241 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_241 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 241 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 241 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_242 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (242 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 242 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 242 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_243 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_243] using dp.rowsRoom 243 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_243] using dp.rowsNext 243 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 244 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_244 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 244 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 244 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_245 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (245 + 1) := by
      rw [ite_eq_left (dec.mpr rfl), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 245 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 245 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_246 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_246] using dp.rowsRoom 246 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_246] using dp.rowsNext 246 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 247 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_247 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 247 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 247 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x184 0xf1000442
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have dec := ValBind.dec_248 dp.np inv.1.body.regBind inv.1.valBind
    have target : (if Crypto.BcondCore.bcondC 1#4 x.regs then x.regs._PC + sign_extend (524286#19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + HeapV2Compose.offsetOf (248 + 1) := by
      rw [ite_eq_right (fun h => by cases dec.mp h), inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    have low : (x.regs._PC + sign_extend (524286#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
      rw [inv.1.body.core.v1.pc, BitVec.add_assoc]
      exact (low_of _ (by decide) dp.low)
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 248 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (DefaultBcondEventTail.W 1#4 524286#19) 69 (by decide) (by decide) x inv.1.body (DefaultBcondEventTail.tail_at real x 1#4 524286#19 (by decide) low _ target) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 248 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x188 0x54ffffc1
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 249 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (EntryBodyRet.W 30#5) 94 (by decide) (by decide) x inv.1.body (DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) (by rw [RtSaved2.link_target (by decide) inv.1.lr]; exact (low_of _ (by decide) dp.low)) _ (RtSaved2.link_target (by decide) inv.1.lr)) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 249 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x18c 0xd65f03c0
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 250 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_250 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 250 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x50 0xaa1303e0
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 250 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x50 0xaa1303e0
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 251 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_251 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 251 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x54 0x910003e1
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 251 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x54 0x910003e1
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    have target : NativeEntryCallerParts.blTarget 78#26 x = base + HeapV2Compose.offsetOf (252 + 1) := by
      rw [NativeEntryCallerRegisters.bl_target, inv.1.body.core.v1.pc, BitVec.add_assoc]
      congr 1 <;> decide
    exact DefaultHeapDitStep.bl real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 252 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      78#26 (by decide) (by decide) x inv.1.body (by rw [target]; exact (low_of _ (by decide) dp.low)) (controls inv.1) target dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 252 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 88 2483028046
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_253 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_253] using dp.rowsRoom 253 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_253] using dp.rowsNext 253 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 254 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_254 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 254 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x194 0x9b037c49
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 254 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x194 0x9b037c49
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 255 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_255 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 255 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x198 0x9bc37c4a
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 255 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x198 0x9bc37c4a
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_256 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_256] using dp.rowsRoom 256 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_256] using dp.rowsNext 256 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 257 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_257 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 257 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1a0 0x9b057c4b
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 257 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1a0 0x9b057c4b
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 258 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_258 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 258 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1a4 0x9bc57c4c
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 258 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1a4 0x9bc57c4c
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 259 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_259 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 259 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1a8 0x9b047c47
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 259 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1a8 0x9b047c47
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 260 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_260 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 260 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1ac 0x9bc47c46
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 260 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1ac 0x9bc47c46
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 261 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_261 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 261 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1b0 0xab07014a
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 261 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1b0 0xab07014a
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 262 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_262 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 262 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1b4 0xba06016b
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 262 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1b4 0xba06016b
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 263 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_263 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 263 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1b8 0x9b047c67
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 263 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1b8 0x9b047c67
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 264 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_264 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 264 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1bc 0x9bc47c66
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 264 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1bc 0x9bc47c66
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 265 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_265 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 265 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1c0 0x9a1f00c6
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 265 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1c0 0x9a1f00c6
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 266 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_266 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 266 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1c4 0xab07016b
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 266 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1c4 0xab07016b
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 267 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_267 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 267 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1c8 0x9b057c8d
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 267 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1c8 0x9b057c8d
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 268 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_268 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 268 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1cc 0x9bc57c8e
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 268 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1cc 0x9bc57c8e
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 269 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_269 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 269 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1d0 0xba06018c
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 269 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1d0 0xba06018c
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  omega
#print axioms dit_segment_08
end ReleaseProfile.DefaultHeapRun
