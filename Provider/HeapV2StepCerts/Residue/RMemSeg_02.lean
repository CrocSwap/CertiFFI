import HeapV2StepCerts.Residue.RunBase
import HeapV2StepCerts.Residue.Step5Mem_02
import HeapV2StepCerts.Residue.Step5Mem_03
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.Residue.Run
open HeapV2StepCerts.E17General
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

run_cmd do
  IO.eprintln "CURRENT_DECL Residue.memSeg_02"
  (← IO.getStderr).flush

theorem memSeg_02 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget)
    (hb : 357 ≤ budget) :
    ∀ k, 120 ≤ k → k < 180 → isMem k = true →
      Uget.Chain.Step real (I5 spec config rows mapping base pins entry budget k) (I5 spec config rows mapping base pins entry budget (k + 1)) := by
  intro k lo hi hm
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_122 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_123 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_126 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_127 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_130 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_131 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_134 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_135 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_138 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_139 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_142 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_143 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
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
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_153 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_156 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_159 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_162 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_165 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_168 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_171 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_174 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact HeapV2StepCerts.Residue.Step5Mem.step5_177 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page (qOf entry) dp.np _ _ entry
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact absurd hm (by decide)
  exact absurd hi (by omega)

#print axioms memSeg_02
end HeapV2StepCerts.Residue.Run
