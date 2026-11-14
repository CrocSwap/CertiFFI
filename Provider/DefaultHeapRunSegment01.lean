-- Current-profile heap body with exact ordered records.
import DefaultHeapRunRecords
import DefaultHeapBranchRows00
import DefaultHeapBranchRows01
import DefaultHeapClassRows00
import DefaultHeapMemoryResidue00
import DefaultHeapMemoryResidue01
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun

#check "CURRENT_DECL default heap segment_01"
theorem segment_01 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 30 ≤ k → k < 60 → DefaultHeapResidue.Step real spec mapping (records spec pins k)
      (RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) (RunInv spec config rows mapping base pins entry budget (k + 1) catalogue capacity drawsBefore) := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_30 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_30] using dp.rowsRoom 30 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_30] using dp.rowsNext 30 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_31 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_31] using dp.rowsRoom 31 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_31] using dp.rowsNext 31 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_32 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 32 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_33 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 33 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_34 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_34] using dp.rowsRoom 34 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_34] using dp.rowsNext 34 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_35 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_35] using dp.rowsRoom 35 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_35] using dp.rowsNext 35 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_36 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 36 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_37 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 37 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_38 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_38] using dp.rowsRoom 38 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_38] using dp.rowsNext 38 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_39 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_39] using dp.rowsRoom 39 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_39] using dp.rowsNext 39 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_40 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 40 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_41 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 41 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_42 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_42] using dp.rowsRoom 42 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_42] using dp.rowsNext 42 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_43 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_43] using dp.rowsRoom 43 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_43] using dp.rowsNext 43 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_44 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 44 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_45 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 45 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_46 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_46] using dp.rowsRoom 46 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_46] using dp.rowsNext 46 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_47 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_47] using dp.rowsRoom 47 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_47] using dp.rowsNext 47 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_48 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 48 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_49 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 49 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_50 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_50] using dp.rowsRoom 50 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_50] using dp.rowsNext 50 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_51 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_51] using dp.rowsRoom 51 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_51] using dp.rowsNext 51 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_52 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 52 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_53 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 53 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_54 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_54] using dp.rowsRoom 54 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_54] using dp.rowsNext 54 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_55 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_55] using dp.rowsRoom 55 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_55] using dp.rowsNext 55 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_56 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 56 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_57 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 57 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_58 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_58] using dp.rowsRoom 58 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_58] using dp.rowsNext 58 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_59 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_59] using dp.rowsRoom 59 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_59] using dp.rowsNext 59 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · omega
  · omega

#print axioms segment_01
end ReleaseProfile.DefaultHeapRun
