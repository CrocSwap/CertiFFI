import ArmCertWalk.StageCanonical
import ArmCertWalk.RawViewFacts
import ArmCertWalk.StructuralInputs
import Walk.S1BlockCheck

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- This exact FINAL-model implementation-defined key is false. It is not
an assumption about hardware features or unrecognized implementation keys. -/
theorem contiguous_guard_false (txsz : BitVec 6) (level : Int) (state : State)
    (valid : 1 ≤ level ∧ level ≤ 3) :
    AArch64_ContiguousBitFaults 0#1 txsz .TGx_4KB level state = .ok false state := by
  simp [AArch64_ContiguousBitFaults, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    S1WalkChecks.contiguous_size level valid state, S1WalkChecks.impdef_contiguous]

theorem amec_nonsecure_false (params : S1TTWParams) (regime : Regime)
    (descriptor : BitVec 64) (state : State) (d128 : params.d128 = 0#1) :
    AArch64_S1AMECFault params .PAS_NonSecure regime descriptor state = .ok false state := by
  have nonrealm : ((.PAS_NonSecure : PASpace) == .PAS_Realm) = false := by decide
  simp [AArch64_S1AMECFault, d128, nonrealm, Sail.BitVec.length, ArmFull.assert, PreSail.assert,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

def blockFaultValue (regs : Regs) (descriptor : BitVec 64) : Bool :=
  if regs.FeatureImpl[101] then
    ((regs.bank_Int .__block_bbm_implemented == 1) || (regs.bank_Int .__block_bbm_implemented == 2)) &&
      descriptor.getLsbD 16
  else false

theorem have_block_bbm_eq (state : State) :
    HaveBlockBBM () state = .ok state.regs.FeatureImpl[101] state := by rfl

/-- All BBM feature/level/nT values are retained as CURRENT primitive data.
No feature-absence or global nT=0 pin is introduced. -/
theorem block_nt_fault_eq (descriptor : BitVec 64) (state : State) :
    AArch64_BlocknTFaults 0#1 descriptor state = .ok (blockFaultValue state.regs descriptor) state := by
  have bit16 := source_permission_bit_unextended descriptor 16 (by decide)
  cases feature : state.regs.FeatureImpl[101] with
  | false =>
    have featureCall : HaveBlockBBM () state = .ok false state := by
      simpa only [feature] using have_block_bbm_eq state
    simp [AArch64_BlocknTFaults, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      featureCall, blockFaultValue, feature]
  | true =>
    have featureCall : HaveBlockBBM () state = .ok true state := by
      simpa only [feature] using have_block_bbm_eq state
    have supportCall : AArch64_BlockBBMSupportLevel () state =
        .ok (state.regs.bank_Int .__block_bbm_implemented) state := by
      simp [AArch64_BlockBBMSupportLevel, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        featureCall, S1BlockCheck.level_key]
      rfl
    cases bit : descriptor.getLsbD 16 <;>
      simp [AArch64_BlocknTFaults, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        featureCall, supportCall, blockFaultValue, feature, bit16, bit,
        S1WalkChecks.impdef_nt, Sail.BitVec.length, ArmFull.assert, PreSail.assert,
        ← BitVec.getLsbD_eq_getElem]

theorem block_fault_view_congr (regs : Regs) (pie ha hd : Bool) (first second : BitVec 64)
    (same : S1DescriptorPIE.view pie ha hd first = S1DescriptorPIE.view pie ha hd second) :
    blockFaultValue regs first = blockFaultValue regs second := by
  have stable : S1Descriptor.stable first = S1Descriptor.stable second :=
    congrArg S1DescriptorPIE.View.stable same
  have bit := S1StablePath.bit_eq first second stable 16 (by decide) (by decide) (by decide)
  simp only [blockFaultValue, bit]

theorem source_af_guard_false (params : S1TTWParams) (descriptor : BitVec 64)
    (ready : AFReady params .leaf descriptor) :
    (((BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 10])) == 0#1) &&
      (params.ha == 0#1)) = false := by
  rw [source_permission_bit descriptor 10 (by decide)]
  change descriptor.getLsbD 10 = true ∨ params.ha = 1#1 at ready
  rcases ready with af | ha
  · simp [af]
  · simp [ha]

#print axioms contiguous_guard_false
#print axioms amec_nonsecure_false
#print axioms block_nt_fault_eq
#print axioms block_fault_view_congr
#print axioms source_af_guard_false
end ArmCertWalk
