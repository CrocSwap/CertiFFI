import ArmCertWalk.OuterTableTotal
import ArmCertWalk.RawViewFacts
import ArmCertTranslateModel.LeafBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Pure source-format data. The actual getter constructs these equalities;
no native call result or preservation answer is an input. -/
structure WalkFormat (params : S1TTWParams) (physical : PhysicalConfig)
    (controls : S1LogicalReference.Controls) : Prop where
  d128 : params.d128 = 0#1
  ds : params.ds = 0#1
  tg : params.tgx = .TGx_4KB
  aie : params.aie = 0#1
  pnch : params.pnch = 0#1
  endian : params.ee = 0#1
  ips : params.ps = physical.ips
  hpd : controls.hpd = (params.hpd == 1#1)

/-- Current primitive inputs of the source callees. Image invariants and their
preservation remain the canonical components, supplied separately. -/
structure WalkCalleesAt (params : S1TTWParams) (physicalConfig : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (config : AttributeConfig) (state : State) : Prop where
  physical : PhysicalAt physicalConfig state
  attributes : ActiveAttributesAt config params state
  permissions : LeafPermissionControls params (outputOverlayEnabled state.regs) controls
  el : state.regs.PSTATE.EL = 0#2 ∨ state.regs.PSTATE.EL = 1#2
  noRME : state.regs.FeatureImpl[232] = false
  aarch64 : state.regs.PSTATE.nRW = 0#1
  el3A64 : state.regs.FeatureImpl[7] = true
  noEL3A32 : state.regs.FeatureImpl[3] = false

theorem WalkCalleesAt.of_regs {params : S1TTWParams} {physicalConfig : PhysicalConfig}
    {controls : S1LogicalReference.Controls} {config : AttributeConfig} {state other : State}
    (current : WalkCalleesAt params physicalConfig controls config state)
    (registers : other.regs = state.regs) : WalkCalleesAt params physicalConfig controls config other := by
  exact ⟨current.physical.of_regs registers, current.attributes.of_regs registers,
    by rw [registers]; exact current.permissions,
    by rw [registers]; exact current.el, by rw [registers]; exact current.noRME,
    by rw [registers]; exact current.aarch64, by rw [registers]; exact current.el3A64,
    by rw [registers]; exact current.noEL3A32⟩

/-- A source-derived slot value identifies the existing physical observation.
This is only the address-data join, not a second topology or byte checker. -/
theorem observed_actual_slot {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (logical : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (observed : logicalObserve spec.logicalRows logical physical view)
    (actual : FullAddress) (slot : actual.address.toNat = logical)
    (space : actual.paspace = .PAS_NonSecure) : actual = physical := by
  have identity := spec.identity logical physical view observed
  have addressEqual : actual.address = physical.address := BitVec.eq_of_toNat_eq (slot.trans identity.1)
  have spaceEqual : actual.paspace = physical.paspace := space.trans identity.2.symm
  cases actual
  cases physical
  congr <;> assumption

#print axioms WalkCalleesAt.of_regs
#print axioms observed_actual_slot
end ArmCertWalk
