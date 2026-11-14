import ReleaseProfile.GB10.SpecTransport
import ReleaseProfile.GB10.SpecWitness

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-!
# SpecAgree for a source-pinned spec

A spec satisfying `SourceSpec rho caller` agrees with any base spec whose walk fields have the GB10
literal values (ha = hd = 1, pie = mtx = 0, txsz = 16, tbi = 1, tbid = nfd = e0pd = 0; controls
hpd = pie = false, regime el20), on every field the closed-membership walk reads. Each source value is
read off the declared TCR_EL2 bits and declared features (HAFDBS, HPDS true; S1PIE false).
-/

namespace ReleaseProfile.GB10.SourceAgree

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.SpecTransport
open ArmFull ArmCertWalk ArmCert.Translate.Model

theorem tcr_bit (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (i : Nat) (hi : i < 64)
    (v : Bool) (a : AuthorityRef)
    (rec : ReleaseProfile.GB10.controlDeclared .TCR_EL2 i = some (v, a)) :
    (controlWord rho.val caller.caller .TCR_EL2).getLsbD i = v :=
  rho.property.construction.control64 caller.caller .TCR_EL2 ⟨i, hi⟩ v a rfl rec

set_option hygiene false in
/-- Close `Sail.BitVec.extractLsb (controlWord …) i i = c` from the declared TCR_EL2 bit `i`. -/
macro "tcr_extract " i:num v:term : tactic => `(tactic| (
  have hb := tcr_bit rho caller $i (by decide) $v _ rfl
  generalize controlWord rho.val caller.caller .TCR_EL2 = w at hb ⊢
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Sail.BitVec.extractLsb, ArmFull.Functions._get_TCR_EL2_Type_TBI0, ArmFull.Functions._get_TCR_EL2_Type_TBID0,
    ArmFull.Functions._get_TCR_EL2_Type_E0PD0, ArmFull.Functions._get_TCR_EL2_Type_NFD0] at hj ⊢
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using hb))

set_option hygiene false in
/-- Close `Sail.BitVec.slice (controlWord …) i 1 = c` from the declared TCR_EL2 bit `i`. -/
macro "tcr_slice " i:num v:term : tactic => `(tactic| (
  have hb := tcr_bit rho caller $i (by decide) $v _ rfl
  generalize controlWord rho.val caller.caller .TCR_EL2 = w at hb ⊢
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have : j = 0 := by omega
  subst this
  simpa [Sail.BitVec.slice, BitVec.getLsbD_extractLsb', BitVec.getLsbD_eq_getElem] using hb))

theorem specAgree_source {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    {domain : QueryDomain} (base spec' : TopologyImageSpec domain) (sspec : SourceSpec rho caller spec')
    (d : DataPart)
    (bha : base.params.ha = 1#1) (bhd : base.params.hd = 1#1) (bpie : base.params.pie = 0#1)
    (bmtx : base.params.mtx = 0#1) (btxsz : base.params.txsz = 16#6) (btbi : base.params.tbi = 1#1)
    (btbid : base.params.tbid = 0#1) (bnfd : base.params.nfd = 0#1) (be0pd : base.params.e0pd = 0#1)
    (bhpd : base.controls.hpd = false) (bpieC : base.controls.pie = false)
    (bregime : base.controls.regime = S1LogicalReference.Regime.el20) :
    SpecAgree base spec'.params spec'.controls := by
  have f47 := sourceRegs_feature rho caller d 47 (by decide) true _ rfl
  have f48 := sourceRegs_feature rho caller d 48 (by decide) true _ rfl
  have f209 := sourceRegs_feature rho caller d 209 (by decide) false _ rfl
  have hw : (sourceRegs rho caller d).bank_BitVec_64 .TCR_EL2 = controlWord rho.val caller.caller .TCR_EL2 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- txsz
    rw [sspec.normalizedTxsz d, hw, sourceT0SZ, normalizeTxsz_16, btxsz]
  · -- tbi
    have h := sspec.guardTbi d
    simp only [translateGuardView, currentHostGuardView, hw] at h
    rw [h, btbi]
    tcr_extract 37 true
  · -- tbid
    have h := sspec.guardTbid d
    simp only [translateGuardView, currentHostGuardView, hw] at h
    rw [h, btbid]
    have hv : ArmFull.Functions._get_TCR_EL2_Type_TBID0 (controlWord rho.val caller.caller .TCR_EL2) = 0#1 := by tcr_extract 51 false
    rw [hv]
    simp only [ite_self]
  · -- mtx
    rw [sspec.paramsMtx d, hw, bmtx]
    have hv : Sail.BitVec.extractLsb (controlWord rho.val caller.caller .TCR_EL2) 60 60 = 0#1 := by tcr_extract 60 false
    rw [hv]
    simp only [ite_self]
  · -- e0pd
    have h := sspec.guardE0pd d
    simp only [translateGuardView, currentHostGuardView, hw] at h
    rw [h, be0pd]
    have hv : ArmFull.Functions._get_TCR_EL2_Type_E0PD0 (controlWord rho.val caller.caller .TCR_EL2) = 0#1 := by tcr_extract 55 false
    rw [hv]
    simp only [ite_self]
  · -- nfd
    have h := sspec.guardNfd d
    simp only [translateGuardView, currentHostGuardView, hw] at h
    rw [h, bnfd]
    have hv : ArmFull.Functions._get_TCR_EL2_Type_NFD0 (controlWord rho.val caller.caller .TCR_EL2) = 0#1 := by tcr_extract 53 false
    rw [hv]
    simp only [ite_self]
  · -- ha
    rw [sspec.paramsHa d, bha]
    unfold hostHA
    rw [if_pos f47, hw]
    tcr_slice 39 true
  · -- hd
    rw [sspec.paramsHd d, bhd]
    unfold hostHD
    rw [if_pos f47, hw]
    tcr_slice 40 true
  · -- pie
    rw [sspec.paramsPie d, bpie]
    unfold hostPIE
    simp [f209]
  · -- table permissions: hpd = pie = false and nv1Mode false in el20, for both
    have hpd' : spec'.controls.hpd = false := by
      rw [sspec.hpd d]
      have f48' : (sourceRegs rho caller d).FeatureImpl[48]! = true := by
        rw [getElem!_pos _ 48 (by decide)]; exact f48
      have b41 : Sail.BitVec.extractLsb (controlWord rho.val caller.caller .TCR_EL2) 41 41 = 0#1 := by
        tcr_extract 41 false
      rw [if_pos f48', hw, b41]
      rfl
    have pie' : spec'.controls.pie = false := by
      rw [sspec.pie d]; unfold hostPIE; simp [f209]
    funext prior desc
    simp only [S1LogicalReference.tablePermissions, S1LogicalReference.nv1Mode, hpd', pie', bhpd, bpieC,
      sspec.regime, bregime]
    rfl

end ReleaseProfile.GB10.SourceAgree

#print axioms ReleaseProfile.GB10.SourceAgree.specAgree_source
