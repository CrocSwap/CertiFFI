-- Current-profile heap body with exact ordered records.
import DefaultHeapRunRecords
import DefaultHeapBranchRows05
import DefaultHeapBranchRowsCall
import DefaultHeapClassRows03
import DefaultHeapClassRows04
import DefaultHeapMemoryResidue04
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun

#check "CURRENT_DECL default heap segment_08"
theorem segment_08 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 240 ≤ k → k < 270 → DefaultHeapResidue.Step real spec mapping (records spec pins k)
      (RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) (RunInv spec config rows mapping base pins entry budget (k + 1) catalogue capacity drawsBefore) := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_240 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_240] using dp.rowsRoom 240 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_240] using dp.rowsNext 240 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_241 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 241 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_242 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 242 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_243 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_243] using dp.rowsRoom 243 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_243] using dp.rowsNext 243 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_244 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 244 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_245 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 245 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_246 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_246] using dp.rowsRoom 246 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_246] using dp.rowsNext 246 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_247 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 247 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_248 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 248 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_249 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 249 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_250 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 250 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_251 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 251 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_252 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 252 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_253 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_253] using dp.rowsRoom 253 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_253] using dp.rowsNext 253 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_254 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 254 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_255 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 255 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_256 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_256] using dp.rowsRoom 256 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_256] using dp.rowsNext 256 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_257 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 257 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_258 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 258 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_259 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 259 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_260 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 260 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_261 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 261 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_262 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 262 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_263 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 263 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_264 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 264 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_265 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 265 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_266 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 266 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_267 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 267 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_268 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 268 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_269 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 269 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · omega
  · omega

#print axioms segment_08
end ReleaseProfile.DefaultHeapRun
