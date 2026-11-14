-- Current-profile heap body with exact ordered records.
import DefaultHeapRunRecords
import DefaultHeapBranchRows02
import DefaultHeapBranchRows03
import DefaultHeapBranchRowsCall
import DefaultHeapClassRows01
import DefaultHeapClassRows02
import DefaultHeapMemoryResidue02
import DefaultHeapMemoryResidue03
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun

#check "CURRENT_DECL default heap segment_04"
theorem segment_04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 120 ≤ k → k < 150 → DefaultHeapResidue.Step real spec mapping (records spec pins k)
      (RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) (RunInv spec config rows mapping base pins entry budget (k + 1) catalogue capacity drawsBefore) := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_120 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 120 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_121 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 121 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_122 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_122] using dp.rowsRoom 122 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_122] using dp.rowsNext 122 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_123 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_123] using dp.rowsRoom 123 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_123] using dp.rowsNext 123 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_124 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 124 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_125 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 125 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_126 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_126] using dp.rowsRoom 126 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_126] using dp.rowsNext 126 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_127 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_127] using dp.rowsRoom 127 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_127] using dp.rowsNext 127 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_128 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 128 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_129 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 129 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_130 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_130] using dp.rowsRoom 130 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_130] using dp.rowsNext 130 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_131 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_131] using dp.rowsRoom 131 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_131] using dp.rowsNext 131 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_132 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 132 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_133 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 133 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_134 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_134] using dp.rowsRoom 134 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_134] using dp.rowsNext 134 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_135 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_135] using dp.rowsRoom 135 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_135] using dp.rowsNext 135 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_136 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 136 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_137 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 137 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_138 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_138] using dp.rowsRoom 138 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_138] using dp.rowsNext 138 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_139 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_139] using dp.rowsRoom 139 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_139] using dp.rowsNext 139 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_140 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 140 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_141 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 141 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_142 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_142] using dp.rowsRoom 142 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_142] using dp.rowsNext 142 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_143 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_143] using dp.rowsRoom 143 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_143] using dp.rowsNext 143 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_144 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 144 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_145 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 145 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_146 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 146 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_147 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 147 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_148 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 148 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_149 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 149 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · omega
  · omega

#print axioms segment_04
end ReleaseProfile.DefaultHeapRun
