-- GENERATED: actual fetched Sub loads, current SSA/profile next invariant; no future callbacks.
import PipeSecpSubPlan.CurrentInv
import PipeSecpSubPlan.SelectedConsumer
import PipeSecpSubPlan.CurrentLoadData
import TranslateSpan.SelectedLoadFacts
import ArmCertPipe.SelectedPairNext
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeSecpSubPlan
theorem current_load_c05_0 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c05) (room : 0 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c05 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view X 0 mapping (selectedSite_c05 inputs 0).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 0).address = true)
    (x : NativeState) (inv : CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 0 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile (0+1) fin ∧
      ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 0 (by rw [plan_length_c05]; decide)) x fin := by
  have old := legacy_current_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 0 x inv
  obtain ⟨member,address⟩ := (selected_site_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 0 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 0#7 = (selectedSite_c05 inputs 0).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c05_0 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c05 inputs 0) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c05 inputs 0) member (by rfl) view X 0 0#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view X 0 mapping (selectedSite_c05 inputs 0).address 0#7 1#5 x source span
  have fetches := selected_fetch_c05 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c05 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x0, 0xa9401825)) (by decide) offset_c05 budget 0 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 5#5 1#5 6#5 0#7 = BitVec.ofNat 32 0xa9401825 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c05 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget _ 0 room page (by decide)
    0#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c05 0 + 4#64 = offset_c05 (0+1) by decide])
    view regions_c05 X 0 binding [(.x 5,none),(.x 6,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 0 (by rw [plan_length_c05]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c05]; decide)
    (compiles_inputs_c05 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c05_0

theorem current_load_c05_1 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c05) (room : 1 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c05 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view Y 0 mapping (selectedSite_c05 inputs 1).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 1).address = true)
    (x : NativeState) (inv : CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile (1+1) fin ∧
      ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 1 (by rw [plan_length_c05]; decide)) x fin := by
  have old := legacy_current_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 1 x inv
  obtain ⟨member,address⟩ := (selected_site_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 1 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 0#7 = (selectedSite_c05 inputs 1).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c05_1 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c05 inputs 1) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c05 inputs 1) member (by rfl) view Y 0 0#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view Y 0 mapping (selectedSite_c05 inputs 1).address 0#7 2#5 x source span
  have fetches := selected_fetch_c05 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c05 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x4, 0xa9400c44)) (by decide) offset_c05 budget 1 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 0#7 = BitVec.ofNat 32 0xa9400c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c05 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget _ 1 room page (by decide)
    0#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c05 1 + 4#64 = offset_c05 (1+1) by decide])
    view regions_c05 Y 0 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 1 (by rw [plan_length_c05]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c05]; decide)
    (compiles_inputs_c05 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c05_1

theorem current_load_c05_4 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c05) (room : 4 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c05 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view X 2 mapping (selectedSite_c05 inputs 4).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 4).address = true)
    (x : NativeState) (inv : CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile (4+1) fin ∧
      ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 4 (by rw [plan_length_c05]; decide)) x fin := by
  have old := legacy_current_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 4 x inv
  obtain ⟨member,address⟩ := (selected_site_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 4 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 2#7 = (selectedSite_c05 inputs 4).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c05_4 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c05 inputs 4) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c05 inputs 4) member (by rfl) view X 2 2#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view X 2 mapping (selectedSite_c05 inputs 4).address 2#7 1#5 x source span
  have fetches := selected_fetch_c05 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c05 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x10, 0xa9412027)) (by decide) offset_c05 budget 4 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 7#5 1#5 8#5 2#7 = BitVec.ofNat 32 0xa9412027 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c05 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget _ 4 room page (by decide)
    2#7 1#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c05 4 + 4#64 = offset_c05 (4+1) by decide])
    view regions_c05 X 2 binding [(.x 7,none),(.x 8,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 4 (by rw [plan_length_c05]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c05]; decide)
    (compiles_inputs_c05 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c05_4

theorem current_load_c05_5 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c05) (room : 5 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c05 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view Y 2 mapping (selectedSite_c05 inputs 5).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c05 inputs 5).address = true)
    (x : NativeState) (inv : CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile (5+1) fin ∧
      ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 5 (by rw [plan_length_c05]; decide)) x fin := by
  have old := legacy_current_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c05 inputs base mapping table) profile 5 x inv
  obtain ⟨member,address⟩ := (selected_site_c05 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 5 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 2#7 = (selectedSite_c05 inputs 5).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c05_5 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c05 inputs 5) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c05 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c05 inputs 5) member (by rfl) view Y 2 2#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view Y 2 mapping (selectedSite_c05 inputs 5).address 2#7 2#5 x source span
  have fetches := selected_fetch_c05 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c05 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x14, 0xa9410c44)) (by decide) offset_c05 budget 5 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 2#7 = BitVec.ofNat 32 0xa9410c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c05 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget _ 5 room page (by decide)
    2#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c05 5 + 4#64 = offset_c05 (5+1) by decide])
    view regions_c05 Y 2 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c05 (getElem (plan_c05 tp) 5 (by rw [plan_length_c05]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c05]; decide)
    (compiles_inputs_c05 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c05_5

theorem current_load_c06_0 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c06) (room : 0 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c06 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view X 0 mapping (selectedSite_c06 inputs 0).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 0).address = true)
    (x : NativeState) (inv : CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 0 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile (0+1) fin ∧
      ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 0 (by rw [plan_length_c06]; decide)) x fin := by
  have old := legacy_current_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 0 x inv
  obtain ⟨member,address⟩ := (selected_site_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 0 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 0#7 = (selectedSite_c06 inputs 0).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c06_0 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c06 inputs 0) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c06 inputs 0) member (by rfl) view X 0 0#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view X 0 mapping (selectedSite_c06 inputs 0).address 0#7 1#5 x source span
  have fetches := selected_fetch_c06 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c06 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x0, 0xa9401825)) (by decide) offset_c06 budget 0 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 5#5 1#5 6#5 0#7 = BitVec.ofNat 32 0xa9401825 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c06 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget _ 0 room page (by decide)
    0#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c06 0 + 4#64 = offset_c06 (0+1) by decide])
    view regions_c06 X 0 binding [(.x 5,none),(.x 6,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 0 (by rw [plan_length_c06]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c06]; decide)
    (compiles_inputs_c06 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c06_0

theorem current_load_c06_1 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c06) (room : 1 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c06 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view X 0 mapping (selectedSite_c06 inputs 1).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 1).address = true)
    (x : NativeState) (inv : CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile (1+1) fin ∧
      ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 1 (by rw [plan_length_c06]; decide)) x fin := by
  have old := legacy_current_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 1 x inv
  obtain ⟨member,address⟩ := (selected_site_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 1 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 0#7 = (selectedSite_c06 inputs 1).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c06_1 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c06 inputs 1) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c06 inputs 1) member (by rfl) view X 0 0#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view X 0 mapping (selectedSite_c06 inputs 1).address 0#7 2#5 x source span
  have fetches := selected_fetch_c06 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c06 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x4, 0xa9400c44)) (by decide) offset_c06 budget 1 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 0#7 = BitVec.ofNat 32 0xa9400c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c06 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget _ 1 room page (by decide)
    0#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c06 1 + 4#64 = offset_c06 (1+1) by decide])
    view regions_c06 X 0 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 1 (by rw [plan_length_c06]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c06]; decide)
    (compiles_inputs_c06 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c06_1

theorem current_load_c06_4 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c06) (room : 4 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c06 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view X 2 mapping (selectedSite_c06 inputs 4).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 4).address = true)
    (x : NativeState) (inv : CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile (4+1) fin ∧
      ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 4 (by rw [plan_length_c06]; decide)) x fin := by
  have old := legacy_current_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 4 x inv
  obtain ⟨member,address⟩ := (selected_site_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 4 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 2#7 = (selectedSite_c06 inputs 4).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c06_4 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c06 inputs 4) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c06 inputs 4) member (by rfl) view X 2 2#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view X 2 mapping (selectedSite_c06 inputs 4).address 2#7 1#5 x source span
  have fetches := selected_fetch_c06 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c06 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x10, 0xa9412027)) (by decide) offset_c06 budget 4 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 7#5 1#5 8#5 2#7 = BitVec.ofNat 32 0xa9412027 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c06 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget _ 4 room page (by decide)
    2#7 1#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c06 4 + 4#64 = offset_c06 (4+1) by decide])
    view regions_c06 X 2 binding [(.x 7,none),(.x 8,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 4 (by rw [plan_length_c06]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c06]; decide)
    (compiles_inputs_c06 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c06_4

theorem current_load_c06_5 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c06) (room : 5 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c06 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view X 2 mapping (selectedSite_c06 inputs 5).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c06 inputs 5).address = true)
    (x : NativeState) (inv : CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile (5+1) fin ∧
      ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 5 (by rw [plan_length_c06]; decide)) x fin := by
  have old := legacy_current_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c06 inputs base mapping table) profile 5 x inv
  obtain ⟨member,address⟩ := (selected_site_c06 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 5 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 2#7 = (selectedSite_c06 inputs 5).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c06_5 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c06 inputs 5) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c06 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c06 inputs 5) member (by rfl) view X 2 2#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view X 2 mapping (selectedSite_c06 inputs 5).address 2#7 2#5 x source span
  have fetches := selected_fetch_c06 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c06 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x14, 0xa9410c44)) (by decide) offset_c06 budget 5 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 2#7 = BitVec.ofNat 32 0xa9410c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c06 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget _ 5 room page (by decide)
    2#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c06 5 + 4#64 = offset_c06 (5+1) by decide])
    view regions_c06 X 2 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c06 (getElem (plan_c06 tp) 5 (by rw [plan_length_c06]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c06]; decide)
    (compiles_inputs_c06 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c06_5

theorem current_load_c07_0 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c07) (room : 0 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c07 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c07 inputs 0).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 0).address = true)
    (x : NativeState) (inv : CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 0 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile (0+1) fin ∧
      ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 0 (by rw [plan_length_c07]; decide)) x fin := by
  have old := legacy_current_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 0 x inv
  obtain ⟨member,address⟩ := (selected_site_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 0 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 0#7 = (selectedSite_c07 inputs 0).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c07_0 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c07 inputs 0) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c07 inputs 0) member (by rfl) view O 0 0#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c07 inputs 0).address 0#7 1#5 x source span
  have fetches := selected_fetch_c07 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c07 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x0, 0xa9401825)) (by decide) offset_c07 budget 0 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 5#5 1#5 6#5 0#7 = BitVec.ofNat 32 0xa9401825 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c07 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget _ 0 room page (by decide)
    0#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c07 0 + 4#64 = offset_c07 (0+1) by decide])
    view regions_c07 O 0 binding [(.x 5,none),(.x 6,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 0 (by rw [plan_length_c07]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c07]; decide)
    (compiles_inputs_c07 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c07_0

theorem current_load_c07_1 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c07) (room : 1 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c07 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view Y 0 mapping (selectedSite_c07 inputs 1).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 1).address = true)
    (x : NativeState) (inv : CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile (1+1) fin ∧
      ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 1 (by rw [plan_length_c07]; decide)) x fin := by
  have old := legacy_current_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 1 x inv
  obtain ⟨member,address⟩ := (selected_site_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 1 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 0#7 = (selectedSite_c07 inputs 1).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c07_1 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c07 inputs 1) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c07 inputs 1) member (by rfl) view Y 0 0#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view Y 0 mapping (selectedSite_c07 inputs 1).address 0#7 2#5 x source span
  have fetches := selected_fetch_c07 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c07 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x4, 0xa9400c44)) (by decide) offset_c07 budget 1 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 0#7 = BitVec.ofNat 32 0xa9400c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c07 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget _ 1 room page (by decide)
    0#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c07 1 + 4#64 = offset_c07 (1+1) by decide])
    view regions_c07 Y 0 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 1 (by rw [plan_length_c07]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c07]; decide)
    (compiles_inputs_c07 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c07_1

theorem current_load_c07_4 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c07) (room : 4 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c07 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c07 inputs 4).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 4).address = true)
    (x : NativeState) (inv : CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile (4+1) fin ∧
      ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 4 (by rw [plan_length_c07]; decide)) x fin := by
  have old := legacy_current_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 4 x inv
  obtain ⟨member,address⟩ := (selected_site_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 4 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 2#7 = (selectedSite_c07 inputs 4).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c07_4 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c07 inputs 4) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c07 inputs 4) member (by rfl) view O 2 2#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c07 inputs 4).address 2#7 1#5 x source span
  have fetches := selected_fetch_c07 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c07 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x10, 0xa9412027)) (by decide) offset_c07 budget 4 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 7#5 1#5 8#5 2#7 = BitVec.ofNat 32 0xa9412027 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c07 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget _ 4 room page (by decide)
    2#7 1#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c07 4 + 4#64 = offset_c07 (4+1) by decide])
    view regions_c07 O 2 binding [(.x 7,none),(.x 8,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 4 (by rw [plan_length_c07]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c07]; decide)
    (compiles_inputs_c07 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c07_4

theorem current_load_c07_5 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c07) (room : 5 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c07 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view Y 2 mapping (selectedSite_c07 inputs 5).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c07 inputs 5).address = true)
    (x : NativeState) (inv : CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile (5+1) fin ∧
      ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 5 (by rw [plan_length_c07]; decide)) x fin := by
  have old := legacy_current_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c07 inputs base mapping table) profile 5 x inv
  obtain ⟨member,address⟩ := (selected_site_c07 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 5 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 2#7 = (selectedSite_c07 inputs 5).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c07_5 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c07 inputs 5) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c07 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c07 inputs 5) member (by rfl) view Y 2 2#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view Y 2 mapping (selectedSite_c07 inputs 5).address 2#7 2#5 x source span
  have fetches := selected_fetch_c07 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c07 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x14, 0xa9410c44)) (by decide) offset_c07 budget 5 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 2#7 = BitVec.ofNat 32 0xa9410c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c07 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c07 budget _ 5 room page (by decide)
    2#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c07 5 + 4#64 = offset_c07 (5+1) by decide])
    view regions_c07 Y 2 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c07 (getElem (plan_c07 tp) 5 (by rw [plan_length_c07]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c07]; decide)
    (compiles_inputs_c07 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c07_5

theorem current_load_c08_0 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c08) (room : 0 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c08 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view X 0 mapping (selectedSite_c08 inputs 0).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 0).address = true)
    (x : NativeState) (inv : CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 0 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile (0+1) fin ∧
      ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 0 (by rw [plan_length_c08]; decide)) x fin := by
  have old := legacy_current_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 0 x inv
  obtain ⟨member,address⟩ := (selected_site_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 0 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 0#7 = (selectedSite_c08 inputs 0).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c08_0 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c08 inputs 0) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c08 inputs 0) member (by rfl) view X 0 0#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view X 0 mapping (selectedSite_c08 inputs 0).address 0#7 1#5 x source span
  have fetches := selected_fetch_c08 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c08 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x0, 0xa9401825)) (by decide) offset_c08 budget 0 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 5#5 1#5 6#5 0#7 = BitVec.ofNat 32 0xa9401825 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c08 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c08 budget _ 0 room page (by decide)
    0#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c08 0 + 4#64 = offset_c08 (0+1) by decide])
    view regions_c08 X 0 binding [(.x 5,none),(.x 6,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 0 (by rw [plan_length_c08]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c08]; decide)
    (compiles_inputs_c08 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c08_0

theorem current_load_c08_1 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c08) (room : 1 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c08 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c08 inputs 1).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 1).address = true)
    (x : NativeState) (inv : CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile (1+1) fin ∧
      ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 1 (by rw [plan_length_c08]; decide)) x fin := by
  have old := legacy_current_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 1 x inv
  obtain ⟨member,address⟩ := (selected_site_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 1 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 0#7 = (selectedSite_c08 inputs 1).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c08_1 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c08 inputs 1) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c08 inputs 1) member (by rfl) view O 0 0#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c08 inputs 1).address 0#7 2#5 x source span
  have fetches := selected_fetch_c08 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c08 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x4, 0xa9400c44)) (by decide) offset_c08 budget 1 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 0#7 = BitVec.ofNat 32 0xa9400c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c08 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c08 budget _ 1 room page (by decide)
    0#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c08 1 + 4#64 = offset_c08 (1+1) by decide])
    view regions_c08 O 0 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 1 (by rw [plan_length_c08]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c08]; decide)
    (compiles_inputs_c08 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c08_1

theorem current_load_c08_4 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c08) (room : 4 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c08 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view X 2 mapping (selectedSite_c08 inputs 4).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 4).address = true)
    (x : NativeState) (inv : CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile (4+1) fin ∧
      ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 4 (by rw [plan_length_c08]; decide)) x fin := by
  have old := legacy_current_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 4 x inv
  obtain ⟨member,address⟩ := (selected_site_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 4 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 2#7 = (selectedSite_c08 inputs 4).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c08_4 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c08 inputs 4) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c08 inputs 4) member (by rfl) view X 2 2#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view X 2 mapping (selectedSite_c08 inputs 4).address 2#7 1#5 x source span
  have fetches := selected_fetch_c08 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c08 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x10, 0xa9412027)) (by decide) offset_c08 budget 4 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 7#5 1#5 8#5 2#7 = BitVec.ofNat 32 0xa9412027 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c08 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c08 budget _ 4 room page (by decide)
    2#7 1#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c08 4 + 4#64 = offset_c08 (4+1) by decide])
    view regions_c08 X 2 binding [(.x 7,none),(.x 8,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 4 (by rw [plan_length_c08]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c08]; decide)
    (compiles_inputs_c08 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c08_4

theorem current_load_c08_5 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c08) (room : 5 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c08 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c08 inputs 5).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c08 inputs 5).address = true)
    (x : NativeState) (inv : CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile (5+1) fin ∧
      ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 5 (by rw [plan_length_c08]; decide)) x fin := by
  have old := legacy_current_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c08 inputs base mapping table) profile 5 x inv
  obtain ⟨member,address⟩ := (selected_site_c08 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 5 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 2#7 = (selectedSite_c08 inputs 5).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c08_5 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c08 inputs 5) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c08 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c08 inputs 5) member (by rfl) view O 2 2#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c08 inputs 5).address 2#7 2#5 x source span
  have fetches := selected_fetch_c08 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c08 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x14, 0xa9410c44)) (by decide) offset_c08 budget 5 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 2#7 = BitVec.ofNat 32 0xa9410c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c08 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c08 budget _ 5 room page (by decide)
    2#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c08 5 + 4#64 = offset_c08 (5+1) by decide])
    view regions_c08 O 2 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c08 (getElem (plan_c08 tp) 5 (by rw [plan_length_c08]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c08]; decide)
    (compiles_inputs_c08 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c08_5

theorem current_load_c09_0 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c09) (room : 0 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c09 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c09 inputs 0).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 0).address = true)
    (x : NativeState) (inv : CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 0 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile (0+1) fin ∧
      ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 0 (by rw [plan_length_c09]; decide)) x fin := by
  have old := legacy_current_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 0 x inv
  obtain ⟨member,address⟩ := (selected_site_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 0 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 0#7 = (selectedSite_c09 inputs 0).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c09_0 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c09 inputs 0) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c09 inputs 0) member (by rfl) view O 0 0#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c09 inputs 0).address 0#7 1#5 x source span
  have fetches := selected_fetch_c09 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c09 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x0, 0xa9401825)) (by decide) offset_c09 budget 0 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 5#5 1#5 6#5 0#7 = BitVec.ofNat 32 0xa9401825 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c09 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c09 budget _ 0 room page (by decide)
    0#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c09 0 + 4#64 = offset_c09 (0+1) by decide])
    view regions_c09 O 0 binding [(.x 5,none),(.x 6,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 0 (by rw [plan_length_c09]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c09]; decide)
    (compiles_inputs_c09 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c09_0

theorem current_load_c09_1 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c09) (room : 1 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c09 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 0 mapping (selectedSite_c09 inputs 1).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 1).address = true)
    (x : NativeState) (inv : CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 1 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile (1+1) fin ∧
      ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 1 (by rw [plan_length_c09]; decide)) x fin := by
  have old := legacy_current_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 1 x inv
  obtain ⟨member,address⟩ := (selected_site_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 1 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 0#7 = (selectedSite_c09 inputs 1).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c09_1 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c09 inputs 1) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c09 inputs 1) member (by rfl) view O 0 0#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 0 mapping (selectedSite_c09 inputs 1).address 0#7 2#5 x source span
  have fetches := selected_fetch_c09 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c09 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x4, 0xa9400c44)) (by decide) offset_c09 budget 1 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 0#7 = BitVec.ofNat 32 0xa9400c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c09 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c09 budget _ 1 room page (by decide)
    0#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c09 1 + 4#64 = offset_c09 (1+1) by decide])
    view regions_c09 O 0 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 1 (by rw [plan_length_c09]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c09]; decide)
    (compiles_inputs_c09 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c09_1

theorem current_load_c09_4 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c09) (room : 4 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c09 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c09 inputs 4).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 4).address = true)
    (x : NativeState) (inv : CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 4 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile (4+1) fin ∧
      ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 4 (by rw [plan_length_c09]; decide)) x fin := by
  have old := legacy_current_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 4 x inv
  obtain ⟨member,address⟩ := (selected_site_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 4 (by decide) x old
  have source : LdpBytes.pairAddr x 1#5 2#7 = (selectedSite_c09 inputs 4).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c09_4 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c09 inputs 4) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c09 inputs 4) member (by rfl) view O 2 2#7 1#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c09 inputs 4).address 2#7 1#5 x source span
  have fetches := selected_fetch_c09 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c09 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x10, 0xa9412027)) (by decide) offset_c09 budget 4 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 7#5 1#5 8#5 2#7 = BitVec.ofNat 32 0xa9412027 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c09 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c09 budget _ 4 room page (by decide)
    2#7 1#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c09 4 + 4#64 = offset_c09 (4+1) by decide])
    view regions_c09 O 2 binding [(.x 7,none),(.x 8,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 4 (by rw [plan_length_c09]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c09]; decide)
    (compiles_inputs_c09 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c09_4

theorem current_load_c09_5 (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes SecpSubPlanScoped.slices) (cb : SecpSubPlanE17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : SecpSubPlanE17.Pins) (budget : Nat)
    (view : Physical.BytePA) (inputs : List (BitVec 64)) (tp : BitVec 64) (profile : AccessProfile)
    (hlen : inputs.length = n0_c09) (room : 5 < budget) (page : base.toNat % 4096 = 0)
    (cs : CodeStaticSecpSubPlan sc mapping base (rowsFootprint spec.imageRows).byte)
    (entry : ArmCertWalk.State)
    (entryClosed : ClosedMembershipAt spec config rows mapping (selectedConsumer_c09 inputs base mapping table) entry)
    (span : TranslateSpan.SelectedBinding.At view O 2 mapping (selectedSite_c09 inputs 5).address)
    (ram : TranslateSpan.SelectedLoadFacts.checkTargets mapping (selectedSite_c09 inputs 5).address = true)
    (x : NativeState) (inv : CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 5 x) :
    ∃ fin, modelStep real x = .ok () fin ∧ CurrentInv_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile (5+1) fin ∧
      ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 5 (by rw [plan_length_c09]; decide)) x fin := by
  have old := legacy_current_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs tp (selectedConsumer_c09 inputs base mapping table) profile 5 x inv
  obtain ⟨member,address⟩ := (selected_site_c09 spec config rows mapping table sc bytes base ifunc p budget view inputs
    (x.regs.bank_BitVec_64 .TPIDR_EL0) hlen).2 5 (by decide) x old
  have source : LdpBytes.pairAddr x 2#5 2#7 = (selectedSite_c09 inputs 5).address := by
    rw [address]; rfl
  obtain ⟨data,payload⟩ := load_payload_c09_5 view inputs tp hlen x inv.extra.1
  have targets := TranslateSpan.SelectedLoadFacts.targets_of_check domain spec config rows mapping table
    (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1)) (selectedSite_c09 inputs 5) member (by rfl) entry entryClosed ram
  have facts := TranslateSpan.SelectedLoadFacts.load_facts domain mapping table (selectedSites_c09 inputs) (SecpSubPlanE17.codeVAs.map (fun (c : Nat × Nat) => MemReloc.imageAddress base c.1))
    (selectedSite_c09 inputs 5) member (by rfl) view O 2 2#7 2#5 x source span targets data payload
  have binding := TranslateSpan.SelectedLoadFacts.binding view O 2 mapping (selectedSite_c09 inputs 5).address 2#7 2#5 x source span
  have fetches := selected_fetch_c09 inputs base mapping table
  have ob := fetchFlexible spec config rows mapping table sc bytes b cb base ifunc p cs (selectedConsumer_c09 inputs base mapping table) fetches (n := 0) (by decide) rfl
    (c := (0x14, 0xa9410c44)) (by decide) offset_c09 budget 5 (by decide) x inv.v2
  have hw : NativeEntryBodyDispatch.Ldp8.selected 4#5 2#5 3#5 2#7 = BitVec.ofNat 32 0xa9410c44 := by decide
  obtain ⟨fin,run,packet,memory,value,pins⟩ := PairSelected.ldp_stepV real domain spec config rows mapping (selectedConsumer_c09 inputs base mapping table)
    sc (referenceImageI bytes base ifunc) base cs.separated base offset_c09 budget _ 5 room page (by decide)
    2#7 2#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) x inv profile inv.extra.2 facts
    (by rw [inv.v2.v1.pc,BitVec.add_assoc,show offset_c09 5 + 4#64 = offset_c09 (5+1) by decide])
    view regions_c09 O 2 binding [(.x 4,none),(.x 3,none)] (by decide) (hw ▸ ob)
  have effect : ArmCertValue.F.Holds view regions_c09 (getElem (plan_c09 tp) 5 (by rw [plan_length_c09]; decide)) x fin := by
    exact ⟨value,memory⟩
  exact ⟨fin,run,ArmCertPipe.SelectedPairNext.of_packet inv (by rw [plan_length_c09]; decide)
    (compiles_inputs_c09 inputs tp hlen) packet effect,effect⟩
#print axioms current_load_c09_5

end PipeSecpSubPlan
