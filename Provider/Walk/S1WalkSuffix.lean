import Walk.S1NormalME
import Walk.S1BlockCheck
import Walk.S2OAFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace S1WalkSuffix
open S1Normality S1NormalME
abbrev Return := FaultRecord × AddressDescriptor × TTWState × BitVec 64

def Safe (r : Regs) : Prop :=
  r.bank_Int .__supported_pa_size = 48 ∧ r.bank_Bool .__tlb_enabled = false

theorem cache_bind (d : BitVec 64) (f : FaultRecord) {α : Type}
    (k : Bool → SailME Return α) (hk : S1NormalME.Normal Safe (k false)) :
    S1NormalME.Normal Safe (S1WalkSuffixSource.cacheGuard 64 d f >>= k) := by
  apply bind_ensures Safe _ _ (fun b => b = false) (fun _ => True)
  · intro s hs
    exact ⟨false, s, S1CacheGuard.disabled d f s hs.2, ⟨rfl, rfl, rfl⟩, rfl⟩
  · intro b hb
    subst b
    exact hk

theorem oa_normal (a : BitVec 56) (ps : BitVec 3) :
    S1NormalME.Normal Safe (monadLift (AArch64_OAOutOfRange a 0#1 ps .TGx_4KB) : SailME Return Bool) := by
  apply lift_conditional
  intro s hs
  rcases S2OAFrame.total a ps s hs.1 with ⟨t, h, hr, hm, he⟩
  exact ⟨_, t, h, hr, hm, he⟩

theorem stage_normal (va : BitVec 64) (w : TTWState) (hl : 1 ≤ w.level ∧ w.level ≤ 3) :
    S1Normality.Normal (StageOA va 0#1 .TGx_4KB w) := by
  intro s
  rcases S1StageOA.total va w s hl with ⟨t, h, hf⟩
  exact ⟨_, t, h, hf⟩

theorem unknown_address : S1Normality.Normal (__UNKNOWN_AddressDescriptor ()) := by
  intro s
  exact S1Unknowns.address_total s

theorem unknown_walk : S1Normality.Normal (__UNKNOWN_TTWState ()) := by
  intro s
  exact S1Unknowns.walkstate_total s

theorem unknown_bits : S1Normality.Normal (__UNKNOWN_bits 64) := by
  intro s
  exact S1Unknowns.bits_total s

-- The statement is on the actual extracted source continuation.
theorem normal (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (ctx : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (slot : FullAddress) (d : BitVec 64) (typ : DescriptorType)
    (f : FaultRecord) (a64 mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (w : TTWState)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB)
    (hl : 1 ≤ w.level ∧ w.level ≤ 3) :
    S1NormalME.Normal Safe
      (S1WalkSuffixSource.suffix wp va regime acc 64 ctx entry
        (aligned, slot, d, typ, f, a64, mro, skl, walkaddr, w)) := by
  unfold S1WalkSuffixSource.suffix
  simp only [hd, htg]
  repeat first
    | exact normal_pure _ _
    | exact oa_normal _ _
    | exact lift_normal Safe _ (stage_normal va w hl)
    | exact lift_normal Safe _ (S1WalkChecks.contiguous_normal wp.txsz w.level hl)
    | exact lift_normal Safe _ (S1BlockCheck.normal d)
    | exact lift_normal Safe _ (S1WalkChecks.amec_normal wp w.baseaddress.paspace regime d hd)
    | exact lift_normal Safe _ unknown_address
    | exact lift_normal Safe _ unknown_walk
    | exact lift_normal Safe _ unknown_bits
    | exact stage_normal va w hl
    | exact S1WalkChecks.contiguous_normal wp.txsz w.level hl
    | exact S1BlockCheck.normal d
    | exact S1WalkChecks.amec_normal wp w.baseaddress.paspace regime d hd
    | exact unknown_address
    | exact unknown_walk
    | exact unknown_bits
    | exact S1Normality.pure_normal _
    | exact lift_normal Safe _ (S1Normality.assert_normal _ _ rfl)
    | exact S1Normality.assert_normal _ _ rfl
    | apply cache_bind
    | apply normal_ite
    | apply normal_bind
    | apply normal_map
    | rw [S1WalkChecks.impdef_af]
    | intro x

#print axioms normal
end S1WalkSuffix
