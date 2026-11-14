import ArmCertTranslateModel.HostFlags

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- The frozen normalization, supplied with actual current register reads. -/
noncomputable def hostNative (state : State) :=
  HostLowerSource.native
    (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .TCR2_EL2)
    (state.regs.bank_BitVec_64 .HCR_EL2) (state.regs.bank_BitVec_64 .SCTLR_EL2)
    (state.regs.bank_BitVec_64 .SCTLR2_EL2) (state.regs.bank_BitVec_64 .SCR_EL3)
    (state.regs.bank_BitVec_64 .MAIR_EL2) (state.regs.bank_BitVec_64 .MAIR2_EL2)
    (state.regs.bank_BitVec_64 .PIR_EL2) (state.regs.bank_BitVec_64 .PIRE0_EL2)
    (state.regs.bank_BitVec_128 ._TTBR0_EL2) (state.regs.bank_BitVec_128 .TTBR1_EL2) state

theorem host_getter_native_eq (state : State) (current : HostRegimeAt state) :
    AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = hostNative state := by
  exact HostLowerSource.complete
    (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .TCR2_EL2)
    (state.regs.bank_BitVec_64 .HCR_EL2) (state.regs.bank_BitVec_64 .SCTLR_EL2)
    (state.regs.bank_BitVec_64 .SCTLR2_EL2) (state.regs.bank_BitVec_64 .SCR_EL3)
    (state.regs.bank_BitVec_64 .MAIR_EL2) (state.regs.bank_BitVec_64 .MAIR2_EL2)
    (state.regs.bank_BitVec_64 .PIR_EL2) (state.regs.bank_BitVec_64 .PIRE0_EL2)
    (state.regs.bank_BitVec_128 ._TTBR0_EL2) (state.regs.bank_BitVec_128 .TTBR1_EL2)
    state current.el3a64 current.noEl3a32 current.noRME current.a64
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    current.tg current.e2h current.d128 current.aie current.pnch current.ds

def HostReadShape (regs : Regs) (params : S1TTWParams) : Prop :=
  params.hpd = (if regs.FeatureImpl[48] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 41 41 else 0#1) ∧
  params.mtx = (if regs.FeatureImpl[191] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 60 60 else 0#1) ∧
  params.wxn = _get_SCTLR_EL2_Type_WXN (regs.bank_BitVec_64 .SCTLR_EL2) ∧
  params.cmow = (if regs.FeatureImpl[167] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .SCTLR_EL2) 32 32 else 0#1) ∧
  (regs.FeatureImpl[209] = true → params.pir = Mk_S1PIRType (regs.bank_BitVec_64 .PIR_EL2) ∧
    params.pire0 = Mk_S1PIRType (regs.bank_BitVec_64 .PIRE0_EL2))

def HostReadGood (regs : Regs) :
    EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok params _ => HostReadShape regs params
  | .error _ _ => False

theorem host_native_reads (state : State) : HostReadGood state.regs (hostNative state) := by
  observe_simp [HostReadGood, HostReadShape, hostNative, HostLowerSource.native]
  intro implemented
  simp [implemented]

/-- The structural admission binding exposes PIR words only when PIE is active.
    NV1 is deliberately absent: the declared EL20 interpretation ignores it. -/
def HostAdmissionShape (regs : Regs) (params : S1TTWParams) : Prop :=
  params.hpd = (if regs.FeatureImpl[48] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 41 41 else 0#1) ∧
  params.mtx = (if regs.FeatureImpl[191] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 60 60 else 0#1) ∧
  params.wxn = _get_SCTLR_EL2_Type_WXN (regs.bank_BitVec_64 .SCTLR_EL2) ∧
  params.cmow = (if regs.FeatureImpl[167] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .SCTLR_EL2) 32 32 else 0#1) ∧
  (params.pie = 1#1 → params.pir = Mk_S1PIRType (regs.bank_BitVec_64 .PIR_EL2) ∧
    params.pire0 = Mk_S1PIRType (regs.bank_BitVec_64 .PIRE0_EL2))

theorem HostFlagShape.pie_supported (flags : HostFlagShape regs params) (active : params.pie = 1#1) :
    regs.FeatureImpl[209] = true := by
  have enabled : hostPIE regs = 1#1 := flags.2.2.1.symm.trans active
  cases feature : regs.FeatureImpl[209] with
  | false => simp [hostPIE, feature] at enabled
  | true => rfl

theorem HostReadShape.admission (reads : HostReadShape regs params) (flags : HostFlagShape regs params) :
    HostAdmissionShape regs params :=
  ⟨reads.1, reads.2.1, reads.2.2.1, reads.2.2.2.1,
    fun active => reads.2.2.2.2 (flags.pie_supported active)⟩

/-- Actual getter success, same-state frame and all requested ACTIVE fields
    follow from current primitive regime facts. No fixed inactive word appears. -/
theorem host_getter_admission_total (state : State) (current : HostRegimeAt state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2)
        (state.regs.bank_BitVec_64 .MAIR_EL2) params ∧
      HostFlagShape state.regs params ∧ HostAdmissionShape state.regs params := by
  obtain ⟨params, next, call, frame, shape, flags⟩ := host_getter_active_total state current
  have reads := host_native_reads state
  rw [← host_getter_native_eq state current, call] at reads
  change HostReadShape state.regs params at reads
  exact ⟨params, next, call, frame, shape, flags, reads.admission flags⟩

theorem HostAdmissionShape.of_regs {state other : State} (shape : HostAdmissionShape state.regs params)
    (registers : other.regs = state.regs) : HostAdmissionShape other.regs params := by
  rw [registers]; exact shape

theorem HostAdmissionShape.guarded_page (state : State) (shape : HostAdmissionShape state.regs params)
    (guarded : Bool) : HostAdmissionShape (gpRegs state.regs guarded) params := shape

#print axioms host_getter_native_eq
#print axioms host_native_reads
#print axioms HostFlagShape.pie_supported
#print axioms host_getter_admission_total
#print axioms HostAdmissionShape.guarded_page
end ArmCert.Translate.Model
