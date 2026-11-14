import Walk.S1WalkSuffix
import ArmCertWalk.PhysicalRange

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk.SuffixNormal
open S1Normality S1NormalME
abbrev Return := S1WalkSuffix.Return

/-- Current implementation controls needed by the source suffix. TLB is the
Sail implementation flag; this record makes no assertion that hardware TLBs
are disabled. Actual source fault choices remain in the returned fault record. -/
structure Safe (config : PhysicalConfig) (regs : Regs) : Prop where
  legal : LegalPAMax config.paMax
  pa : regs.bank_Int .__supported_pa_size = config.paMax
  lpa : regs.FeatureImpl[69] = config.lpa
  lpa2 : regs.FeatureImpl[156] = config.lpa2
  tlb : regs.bank_Bool .__tlb_enabled = false

theorem cache_bind (config : PhysicalConfig) (d : BitVec 64) (fault : FaultRecord) {α : Type}
    (k : Bool → SailME Return α) (next : S1NormalME.Normal (Safe config) (k false)) :
    S1NormalME.Normal (Safe config) (S1WalkSuffixSource.cacheGuard 64 d fault >>= k) := by
  apply bind_ensures (Safe config) _ _ (fun value => value = false) (fun _ => True)
  · intro state current
    exact ⟨false, state, S1CacheGuard.disabled d fault state current.tlb, ⟨rfl, rfl, rfl⟩, rfl⟩
  · intro value equal
    subst value
    exact next

theorem oa_normal (config : PhysicalConfig) (address : BitVec 56) (ips : BitVec 3) :
    S1NormalME.Normal (Safe config)
      (monadLift (AArch64_OAOutOfRange address 0#1 ips .TGx_4KB) : SailME Return Bool) := by
  apply lift_conditional
  intro state current
  let actual := {config with ips := ips}
  have physical : PhysicalAt actual state := ⟨current.legal, current.pa, current.lpa, current.lpa2⟩
  obtain ⟨other, call, registers, memory, events⟩ := oaOutOfRange_total actual address state physical
  exact ⟨_, other, call, registers, memory, events⟩

/-- Actual extracted source continuation: all source fault records and choice
states are retained. The separate leaf admission layer proves fault freedom. -/
theorem normal (config : PhysicalConfig) (params : S1TTWParams) (va : BitVec 64)
    (regime : Regime) (acc : AccessDescriptor) (context : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (slot : FullAddress) (descriptor : BitVec 64) (kind : DescriptorType)
    (fault : FaultRecord) (a64 s2 : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB)
    (level : 1 ≤ current.level ∧ current.level ≤ 3) :
    S1NormalME.Normal (Safe config)
      (S1WalkSuffixSource.suffix params va regime acc 64 context entry
        (aligned, slot, descriptor, kind, fault, a64, s2, skl, walkaddr, current)) := by
  unfold S1WalkSuffixSource.suffix
  simp only [d128, tg]
  repeat first
    | exact normal_pure _ _
    | exact oa_normal config _ _
    | exact lift_normal (Safe config) _ (S1WalkSuffix.stage_normal va current level)
    | exact lift_normal (Safe config) _ (S1WalkChecks.contiguous_normal params.txsz current.level level)
    | exact lift_normal (Safe config) _ (S1BlockCheck.normal descriptor)
    | exact lift_normal (Safe config) _ (S1WalkChecks.amec_normal params current.baseaddress.paspace regime descriptor d128)
    | exact lift_normal (Safe config) _ S1WalkSuffix.unknown_address
    | exact lift_normal (Safe config) _ S1WalkSuffix.unknown_walk
    | exact lift_normal (Safe config) _ S1WalkSuffix.unknown_bits
    | exact S1WalkSuffix.stage_normal va current level
    | exact S1WalkChecks.contiguous_normal params.txsz current.level level
    | exact S1BlockCheck.normal descriptor
    | exact S1WalkChecks.amec_normal params current.baseaddress.paspace regime descriptor d128
    | exact S1WalkSuffix.unknown_address
    | exact S1WalkSuffix.unknown_walk
    | exact S1WalkSuffix.unknown_bits
    | exact S1Normality.pure_normal _
    | exact lift_normal (Safe config) _ (S1Normality.assert_normal _ _ rfl)
    | exact S1Normality.assert_normal _ _ rfl
    | apply cache_bind config
    | apply normal_ite
    | apply normal_bind
    | apply normal_map
    | rw [S1WalkChecks.impdef_af]
    | intro value

#print axioms oa_normal
#print axioms normal
end ArmCertWalk.SuffixNormal
