-- Current-profile heap body with exact ordered records.
import DefaultHeapRunRecords
import DefaultHeapClassRows06
import DefaultHeapClassRows07
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

#check "CURRENT_DECL default heap segment_10"
theorem segment_10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 300 ≤ k → k < 330 → DefaultHeapResidue.Step real spec mapping (records spec pins k)
      (RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) (RunInv spec config rows mapping base pins entry budget (k + 1) catalogue capacity drawsBefore) := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_300 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 300 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_301 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 301 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_302 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 302 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_303 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 303 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_304 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 304 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_305 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 305 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_306 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 306 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_307 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 307 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_308 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 308 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_309 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 309 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_310 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 310 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_311 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 311 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_312 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 312 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_313 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 313 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_314 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 314 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_315 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 315 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_316 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 316 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_317 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 317 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_318 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 318 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_319 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 319 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_320 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 320 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_321 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 321 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_322 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 322 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_323 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 323 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_324 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 324 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_325 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 325 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_326 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 326 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_327 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 327 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_328 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 328 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_329 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_329] using dp.rowsRoom 329 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_329] using dp.rowsNext 329 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · omega
  · omega

#print axioms segment_10
end ReleaseProfile.DefaultHeapRun
