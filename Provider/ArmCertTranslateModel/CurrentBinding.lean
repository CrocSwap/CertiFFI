import ArmCertTranslateModel.HostAdmission
import ArmCertTranslateModel.PermissionImage
import ArmCertWalk.RootEntryNoFault

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Current primitive data binding for canonical EL20 permission controls.
    PIR words are constrained only when PIE is active. This contains no getter
    result, native-call success or invariant-preservation answer. -/
structure HostPermissionControlsAt (regs : Regs) (controls : S1LogicalReference.Controls) : Prop where
  regime : controls.regime = .el20
  ha : controls.ha = (hostHA regs == 1#1)
  hd : controls.hd = (hostHD regs == 1#1)
  pie : controls.pie = (hostPIE regs == 1#1)
  hpd : controls.hpd = ((if regs.FeatureImpl[48] then
    Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 41 41 else 0#1) == 1#1)
  pir : controls.pie = true → controls.pir = Mk_S1PIRType (regs.bank_BitVec_64 .PIR_EL2)
  pire0 : controls.pie = true → controls.pire0 = Mk_S1PIRType (regs.bank_BitVec_64 .PIRE0_EL2)
  overlay : (controls.poe || controls.e0poe) = outputOverlayEnabled regs

/-- Executable current-data check. Inactive PIR/PIRE0 words are not checked. -/
def checkHostPermissionControls (regs : Regs) (controls : S1LogicalReference.Controls) : Bool :=
  decide (controls.regime = .el20) &&
  decide (controls.ha = (hostHA regs == 1#1)) &&
  decide (controls.hd = (hostHD regs == 1#1)) &&
  decide (controls.pie = (hostPIE regs == 1#1)) &&
  decide (controls.hpd = ((if regs.FeatureImpl[48] then
    Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 41 41 else 0#1) == 1#1)) &&
  (!controls.pie || (decide (controls.pir = Mk_S1PIRType (regs.bank_BitVec_64 .PIR_EL2)) &&
    decide (controls.pire0 = Mk_S1PIRType (regs.bank_BitVec_64 .PIRE0_EL2)))) &&
  decide ((controls.poe || controls.e0poe) = outputOverlayEnabled regs)

theorem check_host_permission_controls_sound (regs : Regs) (controls : S1LogicalReference.Controls)
    (checked : checkHostPermissionControls regs controls = true) : HostPermissionControlsAt regs controls := by
  simp only [checkHostPermissionControls, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨⟨regime, ha⟩, hd⟩, pie⟩, hpd⟩, words⟩, overlay⟩ := checked
  have activeWords : controls.pie = true →
      controls.pir = Mk_S1PIRType (regs.bank_BitVec_64 .PIR_EL2) ∧
      controls.pire0 = Mk_S1PIRType (regs.bank_BitVec_64 .PIRE0_EL2) := by
    intro active
    simpa only [active, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] using words
  exact ⟨regime, ha, hd, pie, hpd, fun active => (activeWords active).1,
    fun active => (activeWords active).2, overlay⟩

/-- The model's selected TTBR accessor, including its HTTBR overlay, is reused
    directly. No source call or guessed bank-word alias is a checker input. -/
def checkCurrentLayout (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (regs : Regs) : Bool :=
  decide ((layout.start : Int) = rootStartLevel params) &&
  decide ((layout.inputBits : Int) = AArch64_IASize params.txsz) &&
  decide (layout.root.setWidth 56 = rootBaseValue params (selectedRootTTBR regs va))

theorem check_current_layout_sound (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (regs : Regs) (checked : checkCurrentLayout layout params va regs = true) :
    CurrentLayoutAt layout params va regs := by
  simp only [checkCurrentLayout, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1.1, checked.1.2, checked.2⟩

theorem HostPermissionControlsAt.leaf (current : HostPermissionControlsAt regs controls)
    (flags : HostFlagShape regs params) (reads : HostAdmissionShape regs params) :
    LeafPermissionControls params (outputOverlayEnabled regs) controls := by
  refine ⟨current.regime, ?_, ?_, ?_, ?_, ?_, current.overlay⟩
  · simpa only [flags.2.2.1] using current.pie
  · simpa only [flags.1] using current.ha
  · simpa only [flags.2.1] using current.hd
  · intro active
    have pie : controls.pie = true := by rw [current.pie, ← flags.2.2.1, active]; decide
    exact (current.pir pie).trans ((reads.2.2.2.2 active).1.symm)
  · intro active
    have pie : controls.pie = true := by rw [current.pie, ← flags.2.2.1, active]; decide
    exact (current.pire0 pie).trans ((reads.2.2.2.2 active).2.symm)

theorem HostPermissionControlsAt.hpd_binding (current : HostPermissionControlsAt regs controls)
    (reads : HostAdmissionShape regs params) : controls.hpd = (params.hpd == 1#1) := by
  simpa only [reads.1] using current.hpd

theorem HostPermissionControlsAt.guarded_page (current : HostPermissionControlsAt regs controls) (guarded : Bool) :
    HostPermissionControlsAt (gpRegs regs guarded) controls :=
  ⟨current.regime, current.ha, current.hd, current.pie, current.hpd, current.pir, current.pire0, current.overlay⟩

/-- The actual getter derives the leaf/table control bindings internally from
    current registers. Its inactive undefined fields remain unconstrained. -/
theorem host_getter_permission_controls_total (state : State) (regime : HostRegimeAt state)
    (controls : S1LogicalReference.Controls) (current : HostPermissionControlsAt state.regs controls) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .MAIR_EL2) params ∧
      LeafPermissionControls params (outputOverlayEnabled next.regs) controls ∧
      controls.hpd = (params.hpd == 1#1) := by
  obtain ⟨params, next, call, frame, shape, flags, reads⟩ := host_getter_admission_total state regime
  refine ⟨params, next, call, frame, shape, ?_, current.hpd_binding reads⟩
  rw [frame.1]
  exact current.leaf flags reads

/-- Root geometry inspects TxSZ; other getter fields do not occur in this
    current layout relation. In particular no entire parameter record is fixed. -/
theorem current_layout_reparam (layout : S1LogicalReference.Layout) (first second : S1TTWParams)
    (va : BitVec 64) (regs : Regs) (current : CurrentLayoutAt layout first va regs)
    (txsz : first.txsz = second.txsz) : CurrentLayoutAt layout second va regs := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [rootStartLevel, txsz] using current.start
  · simpa only [txsz] using current.inputBits
  · simpa only [rootBaseValue, rootTableSize, rootStartLevel, txsz] using current.root

theorem current_layout_guarded_page (current : CurrentLayoutAt layout params va regs) (guarded : Bool) :
    CurrentLayoutAt layout params va (gpRegs regs guarded) := ⟨current.start, current.inputBits, current.root⟩

theorem path_start_bound {observe : S1LogicalReference.Observation} {paBits : Nat} {va : BitVec 64}
    {level indexBits : Nat} {base : BitVec 48} {endpoint : S1LogicalReference.PathEnd}
    (path : S1LogicalReference.Path observe paBits va level indexBits base endpoint) : level ≤ 3 := by
  cases path <;> omega

/-- A helper-call composition, not yet the complete native walker prefix.
    M0257 has intervening MECID/cache/attribute/undefined queries whose actual
    returned states and choice effects must be inserted by the source proof.
    The actual getter, actual
    initializer, actual root-entry computation and adjacent actual range check
    share their returned states. Current register geometry and the finite root
    slot bound derive the source results; no callee-success/slot-equality premise
    is supplied. Outer Translate mode selection and the remaining walk are open. -/
theorem topology_root_prefix_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (query : AccessQuery) (member : domain query) (state : State) (regime : HostRegimeAt state)
    (layoutCurrent : CurrentLayoutAt spec.layout spec.params query.va state.regs)
    (txsz : spec.params.txsz = _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2))
    (ips : spec.physicalConfig.ips = _get_TCR_EL2_Type_IPS (state.regs.bank_BitVec_64 .TCR_EL2))
    (physical : PhysicalAt spec.physicalConfig state) :
    ∃ params afterGetter walkstate afterInit entry afterEntry afterRange,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params afterGetter ∧
      AArch64_S1InitialTTWState params query.va .Regime_EL20 .SS_NonSecure afterGetter =
        .ok walkstate afterInit ∧
      AArch64_S1SLTTEntryAddress walkstate.level params query.va walkstate.baseaddress afterInit =
        .ok entry afterEntry ∧
      AArch64_OAOutOfRange entry.address params.d128 params.ps params.tgx afterEntry =
        .ok false afterRange ∧
      entry.address.toNat = S1LogicalReference.entryAddress spec.layout.root query.va spec.layout.start
        (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) ∧
      entry.paspace = .PAS_NonSecure ∧
      nativeTablePermissionProjection walkstate.permissions = ⟨0#2, false, false⟩ ∧
      S1Normality.Frame state afterRange := by
  obtain ⟨params, afterGetter, getterCall, getterFrame, shape, _, _⟩ :=
    host_getter_admission_total state regime
  obtain ⟨tg, d128, aie, pnch, ds, mair, actualTxsz, actualIPS⟩ := shape
  have currentGetter := (current_layout_reparam spec.layout spec.params params query.va state.regs
    layoutCurrent (txsz.trans actualTxsz.symm)).of_regs getterFrame.1
  obtain ⟨walkstate, afterInit, initCall, meaning, level, root, registers, memory, events⟩ :=
    initial_walk_layout_total params query.va afterGetter spec.layout d128 ds tg currentGetter
  have currentInit := currentGetter.of_regs registers
  obtain ⟨_, _, _, _, path, _⟩ := spec.paths query member
  obtain ⟨entry, afterEntry, afterRange, entryCall, rangeCall, space, slot, rangeRegs, rangeMem, rangeEvents⟩ :=
    root_entry_range_total spec.layout params spec.physicalConfig query.va afterInit currentInit
      (physical.of_regs (registers.trans getterFrame.1)) (path_start_bound path) walkstate.baseaddress
      root d128 tg (actualIPS.trans ips.symm) (spec.rootBound query member)
  refine ⟨params, afterGetter, walkstate, afterInit, entry, afterEntry, afterRange,
    getterCall, initCall, ?_, rangeCall, slot, space.trans meaning.2.1,
    meaning.2.2.2.2.2.2.2, ?_⟩
  · simpa only [level] using entryCall
  · exact ⟨rangeRegs.trans (registers.trans getterFrame.1), rangeMem.trans (memory.trans getterFrame.2.1),
      rangeEvents.trans (events.trans getterFrame.2.2)⟩

/-- Optional uniform finite root-table bound. It establishes the existing
    per-query structural bound without traversing or interpreting a walk. -/
def checkRootTableBounds (layout : S1LogicalReference.Layout) (paBits : Nat) : Bool :=
  decide (layout.root.toNat + 8 * 2 ^ (S1LogicalReference.rootBits layout.start layout.inputBits) ≤ 2 ^ paBits)

theorem check_root_table_bounds_sound (layout : S1LogicalReference.Layout) (paBits : Nat)
    (checked : checkRootTableBounds layout paBits = true) (va : BitVec 64) :
    S1LogicalReference.entryAddress layout.root va layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) < 2 ^ paBits := by
  have bound : layout.root.toNat + 8 * 2 ^ (S1LogicalReference.rootBits layout.start layout.inputBits) ≤
      2 ^ paBits := of_decide_eq_true checked
  have index : S1LogicalReference.entryIndex va layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) <
      2 ^ (S1LogicalReference.rootBits layout.start layout.inputBits) := by
    unfold S1LogicalReference.entryIndex
    exact Nat.mod_lt _ (Nat.pow_pos (by decide))
  unfold S1LogicalReference.entryAddress
  omega

theorem path_front_present {observe : S1LogicalReference.Observation} {paBits : Nat} {va : BitVec 64}
    {level indexBits : Nat} {base : BitVec 48} {endpoint : S1LogicalReference.PathEnd}
    (path : S1LogicalReference.Path observe paBits va level indexBits base endpoint) :
    ∃ physical view, observe (S1LogicalReference.entryAddress base va level indexBits) physical view := by
  cases path <;> exact ⟨_, _, by assumption⟩

/-- Recover the current input at any entry of an existing Path, including a
    child table after an earlier update. No root-only layout assumption is used. -/
theorem topology_path_descriptor_inputs {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (state : State) (image : TopologyImageAt spec state)
    {va : BitVec 64} {level indexBits : Nat} {base : BitVec 48} {endpoint : S1LogicalReference.PathEnd}
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows) (effectiveBits spec.physicalConfig).toNat
      va level indexBits base endpoint)
    (entry : FullAddress)
    (slot : entry.address.toNat = S1LogicalReference.entryAddress base va level indexBits)
    (space : entry.paspace = .PAS_NonSecure) :
    ∃ view d,
      logicalObserve spec.logicalRows entry.address.toNat entry view ∧
      S1ByteMemory.DescAt state.mem entry.address.toNat d ∧
      S1DescriptorPIE.view (spec.params.pie == 1#1) (spec.params.ha == 1#1) (spec.params.hd == 1#1) d = view ∧
      entry.address.toNat % 8 = 0 ∧ S2TableRAM.OrdinaryRAM entry.address ∧
      entry.address.toNat ∈ (rowsFootprint spec.imageRows).slots ∧
      (∀ i < 8, (rowsFootprint spec.imageRows).byte (entry.address.toNat + i)) := by
  obtain ⟨physical, view, observed⟩ := path_front_present path
  have identity := spec.identity _ _ _ observed
  have addressEqual : entry.address = physical.address := BitVec.eq_of_toNat_eq (slot.trans identity.1)
  have spaceEqual : entry.paspace = physical.paspace := space.trans identity.2.symm
  have equal : entry = physical := by
    cases entry
    cases physical
    congr <;> assumption
  subst physical
  obtain ⟨leaf, used⟩ := spec.represented _ _ _ observed
  obtain ⟨d, bytes, viewEqual, _⟩ := image _ leaf view used
  have available := spec.available _ _ _ observed
  refine ⟨view, d, ?_, bytes, viewEqual, available.2.1, available.2.2,
    rows_covered spec.imageRows _ leaf view used, ?_⟩
  · simpa only [slot] using observed
  · exact topology_covers spec _ _ _ observed

/-- Join the source-derived root entry address to the current finite byte
    image and physical descriptor footprint. Slot/space equations are the data
    conclusions of the actual root helper, not future-success assumptions.
    The caller must supply the image at its actual current intermediate state. -/
theorem topology_root_descriptor_inputs {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (query : AccessQuery) (member : domain query) (state : State) (image : TopologyImageAt spec state)
    (entry : FullAddress)
    (slot : entry.address.toNat = S1LogicalReference.entryAddress spec.layout.root query.va spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits))
    (space : entry.paspace = .PAS_NonSecure) :
    ∃ view d,
      logicalObserve spec.logicalRows entry.address.toNat entry view ∧
      S1ByteMemory.DescAt state.mem entry.address.toNat d ∧
      S1DescriptorPIE.view (spec.params.pie == 1#1) (spec.params.ha == 1#1) (spec.params.hd == 1#1) d = view ∧
      entry.address.toNat % 8 = 0 ∧ S2TableRAM.OrdinaryRAM entry.address ∧
      entry.address.toNat ∈ (rowsFootprint spec.imageRows).slots ∧
      (∀ i < 8, (rowsFootprint spec.imageRows).byte (entry.address.toNat + i)) := by
  obtain ⟨_, _, _, _, path, _⟩ := spec.paths query member
  exact topology_path_descriptor_inputs spec state image path entry slot space

/-- Actual GP bookkeeping leaves private metadata inputs unchanged. These
    equalities cover this source update only, not the complete Translate call. -/
theorem gp_metadata_inputs (regs : Regs) (guarded : Bool) :
    (gpRegs regs guarded).bank_Int .SEE = regs.bank_Int .SEE ∧
    (gpRegs regs guarded).bank_BitVec_32 ._EDSCR = regs.bank_BitVec_32 ._EDSCR := ⟨rfl, rfl⟩

#print axioms HostPermissionControlsAt.leaf
#print axioms check_host_permission_controls_sound
#print axioms check_current_layout_sound
#print axioms host_getter_permission_controls_total
#print axioms current_layout_reparam
#print axioms topology_root_prefix_total
#print axioms check_root_table_bounds_sound
#print axioms topology_root_descriptor_inputs
#print axioms topology_path_descriptor_inputs
#print axioms gp_metadata_inputs
end ArmCert.Translate.Model
