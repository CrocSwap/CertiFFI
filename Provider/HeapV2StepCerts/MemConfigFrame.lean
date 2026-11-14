-- Memory: register-field frames for the memory-class config predicates, so a
-- ChainInv MemConfig field carries across any step whose listed fields agree.
import ArmCertWalk.OuterModeFacts
import ArmCertWalk.ExistingE11Debug
import ArmCertWalk.TranslateCacheData
import MemM1.MemReadD2
import MemM1.MemWriteD6
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace HeapV2StepCerts.MemConfigFrame
open ArmCertWalk

variable {r r' : Regs}

/-- PostRegs2 reads: SPESampleInFlight, PSTATE.EL/nRW, FeatureImpl, SCR_EL3, HCR_EL2, SCTLR_EL2. -/
theorem post2 (feat : r'.FeatureImpl = r.FeatureImpl) (el : r'.PSTATE.EL = r.PSTATE.EL)
    (nrw : r'.PSTATE.nRW = r.PSTATE.nRW)
    (scr : r'.bank_BitVec_64 .SCR_EL3 = r.bank_BitVec_64 .SCR_EL3)
    (hcr : r'.bank_BitVec_64 .HCR_EL2 = r.bank_BitVec_64 .HCR_EL2)
    (sctlr : r'.bank_BitVec_64 .SCTLR_EL2 = r.bank_BitVec_64 .SCTLR_EL2)
    (spe : r'.bank_Bool .SPESampleInFlight = r.bank_Bool .SPESampleInFlight)
    (h : MemM1.MemReadD2.PostRegs2 r) : MemM1.MemReadD2.PostRegs2 r' :=
  ⟨⟨spe ▸ h.post.spe, el ▸ h.post.el0, nrw ▸ h.post.nrw, feat ▸ h.post.noRME, feat ▸ h.post.vhe,
    feat ▸ h.post.aa64el0, scr ▸ h.post.ns, hcr ▸ h.post.e2h, hcr ▸ h.post.tge, sctlr ▸ h.post.e0e⟩,
    feat ▸ h.noMTE2⟩

/-- PreW reads: PSTATE.EL/nRW, FeatureImpl (incl. TagOK's MTE2 bit), SCR_EL3, HCR_EL2, SCTLR_EL2. -/
theorem preW {acc : AccessDescriptor} (feat : r'.FeatureImpl = r.FeatureImpl) (el : r'.PSTATE.EL = r.PSTATE.EL)
    (nrw : r'.PSTATE.nRW = r.PSTATE.nRW)
    (scr : r'.bank_BitVec_64 .SCR_EL3 = r.bank_BitVec_64 .SCR_EL3)
    (hcr : r'.bank_BitVec_64 .HCR_EL2 = r.bank_BitVec_64 .HCR_EL2)
    (sctlr : r'.bank_BitVec_64 .SCTLR_EL2 = r.bank_BitVec_64 .SCTLR_EL2)
    (h : MemM1.MemWriteD6.PreW acc r) : MemM1.MemWriteD6.PreW acc r' := by
  refine ⟨el ▸ h.el0, nrw ▸ h.nrw, feat ▸ h.noRME, feat ▸ h.vhe, feat ▸ h.aa64el0, scr ▸ h.ns,
    hcr ▸ h.e2h, hcr ▸ h.tge, sctlr ▸ h.e0e, ?_⟩
  have tag := h.tag
  unfold MemM1.MemWriteD5.TagOK at tag ⊢
  rw [feat]; exact tag

/-- currentDCache reads SCTLR_EL2.C. -/
theorem dcache (sctlr : r'.bank_BitVec_64 .SCTLR_EL2 = r.bank_BitVec_64 .SCTLR_EL2)
    (h : currentDCache r = true) : currentDCache r' = true := by
  unfold currentDCache; rw [sctlr]; exact h

/-- HostEL0ModeAt reads FeatureImpl, PSTATE.EL, SCR_EL3, HCR_EL2. -/
theorem mode (feat : r'.FeatureImpl = r.FeatureImpl) (el : r'.PSTATE.EL = r.PSTATE.EL)
    (scr : r'.bank_BitVec_64 .SCR_EL3 = r.bank_BitVec_64 .SCR_EL3)
    (hcr : r'.bank_BitVec_64 .HCR_EL2 = r.bank_BitVec_64 .HCR_EL2)
    (h : HostEL0ModeAt r) : HostEL0ModeAt r' :=
  ⟨feat ▸ h.noEL2A32, feat ▸ h.el2A64, feat ▸ h.vhe, el ▸ h.el, scr ▸ h.ns, hcr ▸ h.tge⟩

/-- ExistingE11DebugAt reads MDSCR_EL1.MDE and EDSCR.HDE. -/
theorem debug (mdscr : r'.bank_BitVec_64 .MDSCR_EL1 = r.bank_BitVec_64 .MDSCR_EL1)
    (hde : _get_EDSCR_Type_HDE (r'.bank_BitVec_32 ._EDSCR) = _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR))
    (h : ExistingE11DebugAt r) : ExistingE11DebugAt r' :=
  ⟨mdscr ▸ h.mde, hde ▸ h.hde⟩

#print axioms post2
#print axioms preW
#print axioms dcache
#print axioms mode
#print axioms debug
end HeapV2StepCerts.MemConfigFrame
