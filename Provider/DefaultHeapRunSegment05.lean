-- Current-profile heap body with exact ordered records.
import DefaultHeapRunRecords
import DefaultHeapBranchRows03
import DefaultHeapBranchRows04
import DefaultHeapBranchRowsCall
import DefaultHeapClassRows02
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

#check "CURRENT_DECL default heap segment_05"
theorem segment_05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 150 ≤ k → k < 180 → DefaultHeapResidue.Step real spec mapping (records spec pins k)
      (RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) (RunInv spec config rows mapping base pins entry budget (k + 1) catalogue capacity drawsBefore) := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_150 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 150 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_151 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 151 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_152 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 152 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_153 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_153] using dp.rowsRoom 153 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_153] using dp.rowsNext 153 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_154 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 154 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_155 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 155 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_156 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_156] using dp.rowsRoom 156 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_156] using dp.rowsNext 156 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_157 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 157 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_158 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 158 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_159 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_159] using dp.rowsRoom 159 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_159] using dp.rowsNext 159 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_160 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 160 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_161 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 161 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_162 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_162] using dp.rowsRoom 162 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_162] using dp.rowsNext 162 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_163 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 163 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_164 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 164 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_165 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_165] using dp.rowsRoom 165 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_165] using dp.rowsNext 165 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_166 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 166 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_167 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 167 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_168 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_168] using dp.rowsRoom 168 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_168] using dp.rowsNext 168 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_169 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 169 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_170 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 170 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_171 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_171] using dp.rowsRoom 171 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_171] using dp.rowsNext 171 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_172 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 172 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_173 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 173 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_174 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_174] using dp.rowsRoom 174 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_174] using dp.rowsNext 174 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_175 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 175 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_176 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 176 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.mem_step_177 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD dp.sep dp.mapped (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (by simpa only [DefaultHeapBudget.cost_at_177] using dp.rowsRoom 177 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_177] using dp.rowsNext 177 (by decide))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.class_step_178 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page  (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 178 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact DefaultHeapBranchRows.step_179 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte catalogue capacity drawsBefore dp.static (by omega) dp.page (low_of _ (by decide) dp.low) (qOf entry) dp.np _ _ entry dp.nodup (Nat.le_trans (Nat.le_add_right _ _) (dp.rowsNext 179 (by decide)))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · omega
  · omega

#print axioms segment_05
end ReleaseProfile.DefaultHeapRun
