import RuntimeClosed
import ReleaseProfile.GB10.WorldSemantics
import ReleaseProfile.RuntimeGB10.WorldDs
import R14GuardWitness.Inputs
import PipeR14Mem.Compat.Cases

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! # Runtime positive C2: case-independent lemmas. Speed mode: compiles. -/

namespace ReleaseProfile.GB10.RuntimeC2

open ArmCertValue ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Runtime

/-- A guard vector with the four flag slots `nb+32..nb+35` replaced (the caller's NZCV). -/
def flagged (l : List (BitVec 64)) (nb : Nat) (n z c v : BitVec 1) : List (BitVec 64) :=
  ((((l.set (nb + 32) (n.setWidth 64)).set (nb + 33) (z.setWidth 64)).set (nb + 34) (c.setWidth 64)).set (nb + 35)
    (v.setWidth 64))

theorem bit1_cases (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  rcases b with ⟨⟨k, hk⟩⟩
  match k, hk with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl
  | k + 2, h => exact absurd h (by omega)

def mappedB (mapping : BitVec 64 → Option Nat) (va : BitVec 64) : Bool :=
  match mapping va with
  | some pa => decide (pa < 2 ^ 56)
  | none => false

theorem mapped_of {mapping : BitVec 64 → Option Nat} {va : BitVec 64} (h : mappedB mapping va = true) :
    ∃ pa, mapping va = some pa ∧ pa < 2 ^ 56 := by
  unfold mappedB at h
  cases hm : mapping va with
  | none => rw [hm] at h; cases h
  | some pa => rw [hm] at h; exact ⟨pa, rfl, of_decide_eq_true h⟩

section lits
variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
  {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}

theorem wxn_lit (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.params.wxn = 0#1 := by
  rw [sspec.paramsWxn d, sourceRegs_bank64 rho caller d .SCTLR_EL2]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_WXN, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using
    rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨19, by decide⟩ false _ rfl rfl

theorem controls_ha_lit (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.controls.ha = true := by
  rw [sspec.ha d, ← sspec.paramsHa d, (sourceSpec_walkLiterals rho caller sspec d).1]
  rfl

theorem controls_hd_lit (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.controls.hd = true := by
  rw [sspec.hd d, ← sspec.paramsHd d, (sourceSpec_walkLiterals rho caller sspec d).2.1]
  rfl

theorem checkAttr_world :
    ArmCert.Translate.Model.checkAttributeImage RuntimeGB10.World.imageRows (sourceAttributes rho caller) = true := by
  have h : ArmCert.Translate.Model.checkAttributeImage RuntimeGB10.World.imageRows (sourceAttributes rho caller) =
      RuntimeGB10.World.imageRows.all (fun row => !row.leaf || decide (ArmCertWalk.reservedAttribute
        (sourceAttributes rho caller).xs (sourceAttributes rho caller).mte2
        (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw)) = false)) :=
    rfl
  rw [h, sourceAttributes_mair rho caller, sourceAttributes_xs rho caller]
  generalize (sourceAttributes rho caller).mte2 = b
  cases b <;> decide

theorem checkWB_world :
    ArmCert.Translate.Model.checkWriteBackAttributeImage RuntimeGB10.World.imageRows (sourceAttributes rho caller) = true := by
  have h : ArmCert.Translate.Model.checkWriteBackAttributeImage RuntimeGB10.World.imageRows (sourceAttributes rho caller) =
      RuntimeGB10.World.imageRows.all (fun row => !row.leaf || ArmCert.Translate.Model.writeBackByte
        (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw))) :=
    rfl
  rw [h, sourceAttributes_mair rho caller]
  decide
end lits

end ReleaseProfile.GB10.RuntimeC2

#print axioms ReleaseProfile.GB10.RuntimeC2.checkAttr_world
