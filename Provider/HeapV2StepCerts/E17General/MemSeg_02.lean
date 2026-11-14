import HeapV2StepCerts.AccShape
import HeapV2StepCerts.ActionTransport
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.BodyMemD
import HeapV2StepCerts.BranchFrame
import HeapV2StepCerts.C3Byte
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.C3Pair
import HeapV2StepCerts.Carry
import HeapV2StepCerts.CodeData
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.DataBytes
import HeapV2StepCerts.FetchFrames
import HeapV2StepCerts.FlagRoots
import HeapV2StepCerts.FlagTails
import HeapV2StepCerts.MemConfigFrame
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.MemNextV4
import HeapV2StepCerts.MemRunD
import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.MemStepsV3
import HeapV2StepCerts.MemStepsV3_00
import HeapV2StepCerts.MemStepsV3_01
import HeapV2StepCerts.MemStepsV3_02
import HeapV2StepCerts.MemStepsV3_03
import HeapV2StepCerts.MemStepsV3_04
import HeapV2StepCerts.MemStepsV3_05
import HeapV2StepCerts.MemStepsV4_02
import HeapV2StepCerts.MemStepsV4_03
import HeapV2StepCerts.MemTailD
import HeapV2StepCerts.MemTailLdrb
import HeapV2StepCerts.MemTailPair
import HeapV2StepCerts.MemTailStrb
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.RegBind
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.RegBindData
import HeapV2StepCerts.RegRootsB
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.Straight
import HeapV2StepCerts.StraightV2
import HeapV2StepCerts.TailW
import HeapV2StepCerts.ValBind
import HeapV2StepCerts.ValBindCore
import HeapV2StepCerts.ValBindData
import HeapV2StepCerts.ValBindSteps01
import HeapV2StepCerts.ValBindSteps02
import HeapV2StepCerts.ValBindSteps03
import HeapV2StepCerts.ValueTailDef
import HeapV2StepCerts.E17General.Base
import Bridge.CruxGenGuarded.Step4Mem.Step4Mem_02
import Bridge.CruxGenGuarded.Step4Mem.Step4Mem_03
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.E17General
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

run_cmd do
  IO.eprintln "CURRENT_DECL E17General.memSeg_02"
  (← IO.getStderr).flush

theorem memSeg_02 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) :
    ∀ k, 120 ≤ k → k < 180 → isMem k = true →
      Uget.Chain.Step real (I4 spec config rows mapping base pins entry budget k) (I4 spec config rows mapping base pins entry budget (k + 1)) := by
  intro k lo hi hm
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_122 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_123 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_126 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_127 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_130 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_131 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_134 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_135 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_138 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_139 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_142 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_143 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_153 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_156 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_159 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_162 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_165 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_168 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_171 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_174 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact Step4Mem.step4_177 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  exact absurd hi (by omega)

#print axioms memSeg_02
end HeapV2StepCerts.E17General
