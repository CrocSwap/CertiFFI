import ArmCertTranslateModel.HostBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

def hostHA (regs : Regs) : BitVec 1 :=
  if regs.FeatureImpl[47]
  then BitVec.slice (regs.bank_BitVec_64 .TCR_EL2) 39 1 else 0#1

def hostHD (regs : Regs) : BitVec 1 :=
  if regs.FeatureImpl[47]
  then BitVec.slice (regs.bank_BitVec_64 .TCR_EL2) 40 1 else 0#1

/-- Exact TCR2 gate in the current declared A64/no-RME host regime. No bit
    in this formula is pinned; the actual feature/current-register values are used. -/
def hostTCR2Enabled (regs : Regs) : Bool :=
  regs.FeatureImpl[178] &&
    (_get_SCR_EL3_Type_TCR2En (regs.bank_BitVec_64 .SCR_EL3) != 0#1) &&
    ((_get_SCRType_NS (Mk_SCRType (regs.bank_BitVec_64 .SCR_EL3)) == 1#1) ||
      (regs.FeatureImpl[117] && (_get_SCR_EL3_Type_EEL2 (regs.bank_BitVec_64 .SCR_EL3) == 1#1)))

def hostPIE (regs : Regs) : BitVec 1 :=
  if regs.FeatureImpl[209] && hostTCR2Enabled regs
  then _get_TCR2_EL2_Type_PIE (regs.bank_BitVec_64 .TCR2_EL2) else 0#1

def hostHAFT (regs : Regs) : BitVec 1 :=
  if regs.FeatureImpl[189] && (hostHA regs == 1#1) && hostTCR2Enabled regs
  then _get_TCR2_EL2_Type_HAFT (regs.bank_BitVec_64 .TCR2_EL2) else 0#1

def HostFlagShape (regs : Regs) (params : S1TTWParams) : Prop :=
  params.ha = hostHA regs ∧ params.hd = hostHD regs ∧ params.pie = hostPIE regs ∧
    params.haft = hostHAFT regs ∧ params.ee = _get_SCTLR_EL2_Type_EE (regs.bank_BitVec_64 .SCTLR_EL2)

def HostFlagGood (regs : Regs) :
    EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok params _ => HostFlagShape regs params
  | .error _ _ => False

theorem host_native_flags (state : State) (current : HostRegimeAt state) :
    HostFlagGood state.regs
      (HostLowerSource.native
        (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .TCR2_EL2)
        (state.regs.bank_BitVec_64 .HCR_EL2) (state.regs.bank_BitVec_64 .SCTLR_EL2)
        (state.regs.bank_BitVec_64 .SCTLR2_EL2) (state.regs.bank_BitVec_64 .SCR_EL3)
        (state.regs.bank_BitVec_64 .MAIR_EL2) (state.regs.bank_BitVec_64 .MAIR2_EL2)
        (state.regs.bank_BitVec_64 .PIR_EL2) (state.regs.bank_BitVec_64 .PIRE0_EL2)
        (state.regs.bank_BitVec_128 ._TTBR0_EL2) (state.regs.bank_BitVec_128 .TTBR1_EL2) state) := by
  observe_simp [HostFlagGood, HostFlagShape, hostHA, hostHD, hostPIE,
    hostHAFT, hostTCR2Enabled, HostLowerSource.native]
  constructor
  · simp only [_get_SCR_EL3_Type_TCR2En, _get_SCRType_NS,
      _get_SCR_EL3_Type_EEL2, _get_TCR2_EL2_Type_PIE, and_assoc]
    split
    · rename_i enabled
      have zero := current.d128 enabled.2.1
      change Sail.BitVec.extractLsb (state.regs.bank_BitVec_64 .TCR2_EL2) 5 5 = 0#1 at zero
      simp only [zero, BitVec.reduceEq, ↓reduceIte]
    · rfl
  · simp only [_get_SCR_EL3_Type_TCR2En, _get_SCRType_NS, _get_SCR_EL3_Type_EEL2, and_assoc]

/-- The active flag fields of the ACTUAL getter are conclusions. Inactive
    parameters and their oracle/occurrence history remain the actual values. -/
theorem host_getter_active_total (state : State) (current : HostRegimeAt state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2)
        (state.regs.bank_BitVec_64 .MAIR_EL2) params ∧ HostFlagShape state.regs params := by
  obtain ⟨params, next, call, frame, shape⟩ := host_getter_total state current
  have flags := host_native_flags state current
  have actual := HostLowerSource.complete
    (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .TCR2_EL2)
    (state.regs.bank_BitVec_64 .HCR_EL2) (state.regs.bank_BitVec_64 .SCTLR_EL2)
    (state.regs.bank_BitVec_64 .SCTLR2_EL2) (state.regs.bank_BitVec_64 .SCR_EL3)
    (state.regs.bank_BitVec_64 .MAIR_EL2) (state.regs.bank_BitVec_64 .MAIR2_EL2)
    (state.regs.bank_BitVec_64 .PIR_EL2) (state.regs.bank_BitVec_64 .PIRE0_EL2)
    (state.regs.bank_BitVec_128 ._TTBR0_EL2) (state.regs.bank_BitVec_128 .TTBR1_EL2)
    state current.el3a64 current.noEl3a32 current.noRME current.a64
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    current.tg current.e2h current.d128 current.aie current.pnch current.ds
  rw [← actual, call] at flags
  exact ⟨params, next, call, frame, shape, flags⟩

theorem HostFlagShape.of_regs {state other : State} (shape : HostFlagShape state.regs params)
    (registers : other.regs = state.regs) : HostFlagShape other.regs params := by
  rw [registers]; exact shape

theorem HostFlagShape.guarded_page (state : State) (shape : HostFlagShape state.regs params)
    (guarded : Bool) : HostFlagShape (gpRegs state.regs guarded) params := shape

theorem HostFlagShape.little_endian {state : State} (shape : HostFlagShape state.regs params)
    (e3 : _get_SCTLR_EL2_Type_EE (state.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1) :
    params.ee = 0#1 := shape.2.2.2.2.trans e3

/-- Match only the source-active image controls. The old static parameters
    may have different inactive words from this actual getter invocation. -/
theorem host_getter_rebinds_image {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (state : State)
    (current : HostRegimeAt state) (bound : HostFlagShape state.regs spec.params)
    (image : TopologyImageAt spec state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2)
        (state.regs.bank_BitVec_64 .MAIR_EL2) params ∧
      HostFlagShape next.regs params ∧ HostRegimeAt next ∧
      TopologyImageAt {spec with params := params} next := by
  obtain ⟨params, next, call, frame, shape, flags⟩ := host_getter_active_total state current
  refine ⟨params, next, call, frame, shape, flags.of_regs frame.1,
    current.of_regs frame.1, ?_⟩
  apply (topology_image_reparam spec next params
    (flags.2.2.1.trans bound.2.2.1.symm)
    (flags.1.trans bound.1.symm) (flags.2.1.trans bound.2.1.symm)).mpr
  unfold TopologyImageAt
  rw [frame.2.1]
  exact image

theorem flag_feature_indices : num_of_Feature .FEAT_HAFDBS = 47 ∧
    num_of_Feature .FEAT_HAFT = 189 ∧ num_of_Feature .FEAT_S1PIE = 209 ∧
    num_of_Feature .FEAT_TCR2 = 178 ∧ num_of_Feature .FEAT_SEL2 = 117 := by decide

#print axioms host_native_flags
#print axioms host_getter_active_total
#print axioms HostFlagShape.guarded_page
#print axioms HostFlagShape.little_endian
#print axioms host_getter_rebinds_image
#print axioms flag_feature_indices
end ArmCert.Translate.Model
