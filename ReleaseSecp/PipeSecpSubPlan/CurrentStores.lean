-- GENERATED: actual fetched Sub stores, current SSA/profile next invariant; no future callbacks.
import PipeSecpSubPlan.CurrentInv
import PipeSecpSubPlan.SelectedConsumer
import PipeSecpSubPlan.CurrentLoadData
import TranslateSpan.SelectedLoadFacts
import TranslateSpan.SelectedStoreFacts
import ArmCertPipe.SelectedPairNext
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeSecpSubPlan
theorem current_store_c05_15 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c05) (room : 15 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c05 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c05 inputs 15).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 15).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (injective : Physical.RegionsInjective view regions_c05)
    (x : NativeState) (inv : CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 15 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile (15+1) fin ∧
      ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 15 (by rw [plan_length_c05]; decide)) x fin := by
  have old := legacy_current_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 15 x inv
  obtain ⟨member,address⟩ := (selected_site_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 15 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 0#7 = (selectedSite_c05 inputs 15).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c05 inputs 15) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c05 inputs 15) member (by rfl) view O 0 0#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c05 inputs 15).address 0#7 0#5 x source span
  have fetches := selected_fetch_c05 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c05 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x3c, 0xa9001805)) (by decide) offset_c05 budget 15 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 5#5 0#5 6#5 0#7 = BitVec.ofNat 32 0xa9001805 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c05 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget _ 15 room page (by decide)
    0#7 0#5 5#5 6#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c05 15 + 4#64 = offset_c05 (15+1) by decide])
    view regions_c05 O 0 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 15 (by rw [plan_length_c05]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c05]; decide)
    (compiles_inputs_c05 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c05_15

theorem current_store_c05_16 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c05) (room : 16 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c05 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c05 inputs 16).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 16).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (injective : Physical.RegionsInjective view regions_c05)
    (x : NativeState) (inv : CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 16 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile (16+1) fin ∧
      ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 16 (by rw [plan_length_c05]; decide)) x fin := by
  have old := legacy_current_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 16 x inv
  obtain ⟨member,address⟩ := (selected_site_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 16 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 2#7 = (selectedSite_c05 inputs 16).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c05 inputs 16) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c05 inputs 16) member (by rfl) view O 2 2#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c05 inputs 16).address 2#7 0#5 x source span
  have fetches := selected_fetch_c05 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c05 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x40, 0xa9012007)) (by decide) offset_c05 budget 16 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 7#5 0#5 8#5 2#7 = BitVec.ofNat 32 0xa9012007 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c05 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget _ 16 room page (by decide)
    2#7 0#5 7#5 8#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c05 16 + 4#64 = offset_c05 (16+1) by decide])
    view regions_c05 O 2 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 16 (by rw [plan_length_c05]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c05]; decide)
    (compiles_inputs_c05 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c05_16

theorem current_store_c06_15 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c06) (room : 15 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c06 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c06 inputs 15).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 15).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (injective : Physical.RegionsInjective view regions_c06)
    (x : NativeState) (inv : CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 15 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile (15+1) fin ∧
      ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 15 (by rw [plan_length_c06]; decide)) x fin := by
  have old := legacy_current_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 15 x inv
  obtain ⟨member,address⟩ := (selected_site_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 15 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 0#7 = (selectedSite_c06 inputs 15).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c06 inputs 15) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c06 inputs 15) member (by rfl) view O 0 0#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c06 inputs 15).address 0#7 0#5 x source span
  have fetches := selected_fetch_c06 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c06 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x3c, 0xa9001805)) (by decide) offset_c06 budget 15 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 5#5 0#5 6#5 0#7 = BitVec.ofNat 32 0xa9001805 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c06 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget _ 15 room page (by decide)
    0#7 0#5 5#5 6#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c06 15 + 4#64 = offset_c06 (15+1) by decide])
    view regions_c06 O 0 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 15 (by rw [plan_length_c06]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c06]; decide)
    (compiles_inputs_c06 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c06_15

theorem current_store_c06_16 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c06) (room : 16 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c06 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c06 inputs 16).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 16).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (injective : Physical.RegionsInjective view regions_c06)
    (x : NativeState) (inv : CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 16 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile (16+1) fin ∧
      ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 16 (by rw [plan_length_c06]; decide)) x fin := by
  have old := legacy_current_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 16 x inv
  obtain ⟨member,address⟩ := (selected_site_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 16 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 2#7 = (selectedSite_c06 inputs 16).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c06 inputs 16) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c06 inputs 16) member (by rfl) view O 2 2#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c06 inputs 16).address 2#7 0#5 x source span
  have fetches := selected_fetch_c06 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c06 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x40, 0xa9012007)) (by decide) offset_c06 budget 16 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 7#5 0#5 8#5 2#7 = BitVec.ofNat 32 0xa9012007 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c06 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget _ 16 room page (by decide)
    2#7 0#5 7#5 8#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c06 16 + 4#64 = offset_c06 (16+1) by decide])
    view regions_c06 O 2 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 16 (by rw [plan_length_c06]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c06]; decide)
    (compiles_inputs_c06 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c06_16

theorem current_store_c07_15 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c07) (room : 15 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c07 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c07 inputs 15).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 15).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (injective : Physical.RegionsInjective view regions_c07)
    (x : NativeState) (inv : CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 15 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile (15+1) fin ∧
      ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 15 (by rw [plan_length_c07]; decide)) x fin := by
  have old := legacy_current_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 15 x inv
  obtain ⟨member,address⟩ := (selected_site_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 15 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 0#7 = (selectedSite_c07 inputs 15).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c07 inputs 15) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c07 inputs 15) member (by rfl) view O 0 0#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c07 inputs 15).address 0#7 0#5 x source span
  have fetches := selected_fetch_c07 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c07 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x3c, 0xa9001805)) (by decide) offset_c07 budget 15 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 5#5 0#5 6#5 0#7 = BitVec.ofNat 32 0xa9001805 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c07 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget _ 15 room page (by decide)
    0#7 0#5 5#5 6#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c07 15 + 4#64 = offset_c07 (15+1) by decide])
    view regions_c07 O 0 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 15 (by rw [plan_length_c07]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c07]; decide)
    (compiles_inputs_c07 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c07_15

theorem current_store_c07_16 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c07) (room : 16 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c07 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c07 inputs 16).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 16).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (injective : Physical.RegionsInjective view regions_c07)
    (x : NativeState) (inv : CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 16 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile (16+1) fin ∧
      ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 16 (by rw [plan_length_c07]; decide)) x fin := by
  have old := legacy_current_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 16 x inv
  obtain ⟨member,address⟩ := (selected_site_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 16 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 2#7 = (selectedSite_c07 inputs 16).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c07 inputs 16) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c07 inputs 16) member (by rfl) view O 2 2#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c07 inputs 16).address 2#7 0#5 x source span
  have fetches := selected_fetch_c07 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c07 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x40, 0xa9012007)) (by decide) offset_c07 budget 16 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 7#5 0#5 8#5 2#7 = BitVec.ofNat 32 0xa9012007 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c07 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget _ 16 room page (by decide)
    2#7 0#5 7#5 8#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c07 16 + 4#64 = offset_c07 (16+1) by decide])
    view regions_c07 O 2 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 16 (by rw [plan_length_c07]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c07]; decide)
    (compiles_inputs_c07 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c07_16

theorem current_store_c08_15 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c08) (room : 15 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c08 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c08 inputs 15).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 15).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (injective : Physical.RegionsInjective view regions_c08)
    (x : NativeState) (inv : CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 15 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile (15+1) fin ∧
      ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 15 (by rw [plan_length_c08]; decide)) x fin := by
  have old := legacy_current_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 15 x inv
  obtain ⟨member,address⟩ := (selected_site_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 15 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 0#7 = (selectedSite_c08 inputs 15).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c08 inputs 15) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c08 inputs 15) member (by rfl) view O 0 0#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c08 inputs 15).address 0#7 0#5 x source span
  have fetches := selected_fetch_c08 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c08 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x3c, 0xa9001805)) (by decide) offset_c08 budget 15 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 5#5 0#5 6#5 0#7 = BitVec.ofNat 32 0xa9001805 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c08 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c08 budget _ 15 room page (by decide)
    0#7 0#5 5#5 6#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c08 15 + 4#64 = offset_c08 (15+1) by decide])
    view regions_c08 O 0 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 15 (by rw [plan_length_c08]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c08]; decide)
    (compiles_inputs_c08 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c08_15

theorem current_store_c08_16 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c08) (room : 16 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c08 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c08 inputs 16).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 16).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (injective : Physical.RegionsInjective view regions_c08)
    (x : NativeState) (inv : CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 16 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile (16+1) fin ∧
      ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 16 (by rw [plan_length_c08]; decide)) x fin := by
  have old := legacy_current_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 16 x inv
  obtain ⟨member,address⟩ := (selected_site_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 16 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 2#7 = (selectedSite_c08 inputs 16).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c08 inputs 16) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c08 inputs 16) member (by rfl) view O 2 2#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c08 inputs 16).address 2#7 0#5 x source span
  have fetches := selected_fetch_c08 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c08 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x40, 0xa9012007)) (by decide) offset_c08 budget 16 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 7#5 0#5 8#5 2#7 = BitVec.ofNat 32 0xa9012007 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c08 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c08 budget _ 16 room page (by decide)
    2#7 0#5 7#5 8#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c08 16 + 4#64 = offset_c08 (16+1) by decide])
    view regions_c08 O 2 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 16 (by rw [plan_length_c08]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c08]; decide)
    (compiles_inputs_c08 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c08_16

theorem current_store_c09_15 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c09) (room : 15 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c09 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c09 inputs 15).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 15).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 0 D)
    (injective : Physical.RegionsInjective view regions_c09)
    (x : NativeState) (inv : CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 15 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile (15+1) fin ∧
      ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 15 (by rw [plan_length_c09]; decide)) x fin := by
  have old := legacy_current_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 15 x inv
  obtain ⟨member,address⟩ := (selected_site_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 15 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 0#7 = (selectedSite_c09 inputs 15).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c09 inputs 15) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c09 inputs 15) member (by rfl) view O 0 0#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c09 inputs 15).address 0#7 0#5 x source span
  have fetches := selected_fetch_c09 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c09 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x3c, 0xa9001805)) (by decide) offset_c09 budget 15 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 5#5 0#5 6#5 0#7 = BitVec.ofNat 32 0xa9001805 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c09 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c09 budget _ 15 room page (by decide)
    0#7 0#5 5#5 6#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c09 15 + 4#64 = offset_c09 (15+1) by decide])
    view regions_c09 O 0 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 15 (by rw [plan_length_c09]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c09]; decide)
    (compiles_inputs_c09 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c09_15

theorem current_store_c09_16 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c09) (room : 16 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c09 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c09 inputs 16).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 16).address = true)
    (D : Nat → Prop) (codeD : ImageTableSeparated sc base mapping D)
    (output : TranslateSpan.SelectedStoreFacts.OutputSafe spec view O 2 D)
    (injective : Physical.RegionsInjective view regions_c09)
    (x : NativeState) (inv : CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 16 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile (16+1) fin ∧
      ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 16 (by rw [plan_length_c09]; decide)) x fin := by
  have old := legacy_current_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 16 x inv
  obtain ⟨member,address⟩ := (selected_site_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 16 (by decide) x old
  have source : LdpBytes.pairAddr x 0#5 2#7 = (selectedSite_c09 inputs 16).address := by
    rw [address]; rfl
  have targets := TranslateSpan.SelectedStoreFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c09 inputs 16) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedStoreFacts.store_facts domain spec mapping table D (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c09 inputs 16) member (by rfl) view O 2 2#7 0#5 x source span targets output
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c09 inputs 16).address 2#7 0#5 x source span
  have fetches := selected_fetch_c09 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c09 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x40, 0xa9012007)) (by decide) offset_c09 budget 16 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Stp8.selected 7#5 0#5 8#5 2#7 = BitVec.ofNat 32 0xa9012007 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.stp_stepV real domain spec config rows mapping (selectedConsumer_c09 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c09 budget _ 16 room page (by decide)
    2#7 0#5 7#5 8#5 (by decide) (by decide) (by decide) x inv profile inv.extra.2 D codeD facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c09 16 + 4#64 = offset_c09 (16+1) by decide])
    view regions_c09 O 2 binding (by decide) (by decide) injective [] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 16 (by rw [plan_length_c09]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c09]; decide)
    (compiles_inputs_c09 inputs tp hlen) packet effect,effect⟩
#print axioms current_store_c09_16

end PipeSecpSubPlan
