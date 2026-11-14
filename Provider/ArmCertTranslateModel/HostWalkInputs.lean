import ArmCertTranslateModel.NativeWalkBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Current primitive host/profile data for the actual getter and walk. The
    actual producer binds these fields to its existing implementation profile.
    No source-success, future preservation or whole parameter equality occurs. -/
structure HostWalkAt (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (physicalConfig : PhysicalConfig) (state : State) : Prop where
  regime : HostRegimeAt state
  controls : HostPermissionControlsAt state.regs controls
  physical : PhysicalAt physicalConfig state
  ips : physicalConfig.ips = _get_TCR_EL2_Type_IPS (state.regs.bank_BitVec_64 .TCR_EL2)
  endian : _get_SCTLR_EL2_Type_EE (state.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1
  mair : config.mair = state.regs.bank_BitVec_64 .MAIR_EL2
  xs : state.regs.FeatureImpl[166] = config.xs
  mte2 : state.regs.FeatureImpl[134] = config.mte2
  el : state.regs.PSTATE.EL = 0#2 ∨ state.regs.PSTATE.EL = 1#2

theorem HostWalkAt.getter_inputs {config : AttributeConfig} {controls : S1LogicalReference.Controls}
    {physicalConfig : PhysicalConfig} {state : State} (current : HostWalkAt config controls physicalConfig state)
    (params : S1TTWParams)
    (shape : HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .MAIR_EL2) params)
    (flags : HostFlagShape state.regs params) (reads : HostAdmissionShape state.regs params) :
    WalkFormat params physicalConfig controls ∧ WalkCalleesAt params physicalConfig controls config state := by
  obtain ⟨tg, d128, aie, pnch, ds, mair, txsz, ips⟩ := shape
  exact ⟨⟨d128, ds, tg, aie, pnch, flags.2.2.2.2.trans current.endian,
      ips.trans current.ips.symm, current.controls.hpd_binding reads⟩,
    ⟨current.physical, ⟨mair.trans current.mair.symm, current.xs, current.mte2⟩,
      current.controls.leaf flags reads, current.el, current.regime.noRME, current.regime.a64,
      current.regime.el3a64, current.regime.noEl3a32⟩⟩

/-- The actual getter derives every native-walk input from current primitive
    fields and rebinds all current images and geometry on its SAME successor.
    Whole records and inactive MAIR2/PIR words are left unconstrained. -/
theorem host_getter_walk_inputs_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (query : AccessQuery) (state : State)
    (current : HostWalkAt config spec.controls spec.physicalConfig state)
    (bound : HostImageParamsAt state.regs spec.params)
    (layout : CurrentLayoutAt spec.layout spec.params query.va state.regs)
    (images : CurrentImagesAt spec config rows state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧ ImageParamsEq spec.params params ∧
      CurrentImagesAt {spec with params := params} config rows next ∧
      WalkFormat params spec.physicalConfig spec.controls ∧
      WalkCalleesAt params spec.physicalConfig spec.controls config next ∧
      CurrentLayoutAt spec.layout params query.va next.regs ∧ params.disch = 0#1 := by
  obtain ⟨params, next, call, frame, shape, flags, reads, disch, active, afterImages, leaf, hpd⟩ :=
    host_getter_current_images_total spec config rows state current.regime bound current.controls images
  obtain ⟨format, callees⟩ := current.getter_inputs params shape flags reads
  have actualLayout := (current_layout_reparam spec.layout spec.params params query.va state.regs layout active.txsz).of_regs frame.1
  exact ⟨params, next, call, frame, active, afterImages, format, callees.of_regs frame.1, actualLayout, disch⟩

#print axioms HostWalkAt.getter_inputs
#print axioms host_getter_walk_inputs_total
end ArmCert.Translate.Model
