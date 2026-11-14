import ArmCertTranslateModel.TranslateResultFieldsBinding
import ArmCertWalk.NativeFullTranslateTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- The existing caller's current EL0 host-mode subset transports by selected
    fields of an actual phase frame. These fields are existing E1/F6/F15 data;
    this adds neither a processor pin nor a future source-query answer. -/
theorem host_el0_mode_register_fields {before after : Regs} (mode : HostEL0ModeAt before)
    (features : after.FeatureImpl = before.FeatureImpl)
    (el : after.PSTATE.EL = before.PSTATE.EL)
    (scr : after.bank_BitVec_64 .SCR_EL3 = before.bank_BitVec_64 .SCR_EL3)
    (hcr : after.bank_BitVec_64 .HCR_EL2 = before.bank_BitVec_64 .HCR_EL2) :
    HostEL0ModeAt after := by
  refine ⟨?_, ?_, ?_, el.trans mode.el, ?_, ?_⟩
  · simpa only [features] using mode.noEL2A32
  · simpa only [features] using mode.el2A64
  · simpa only [features] using mode.vhe
  · simpa only [scr] using mode.ns
  · simpa only [hcr] using mode.tge

/-- One actual FullTranslate call retains all current image/query inputs on
    its SAME successor. The existing source proof threads its real mode/fault/
    ignored-value choices and derives the no-stage-two branch. -/
theorem current_full_translate_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (data : S1AccessData spec config rows query)
    (initial : State) (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (mode : HostEL0ModeAt initial.regs) :
    ∃ address fault other,
      AArch64_FullTranslate query.va query.request.raw query.request.aligned initial = .ok address other ∧
      CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial (fault, address) other ∧
      CurrentS1At spec config rows other ∧ CurrentS1AccessAt spec config rows mapping query data other ∧
      HostEL0ModeAt other.regs ∧
      ArmCert.Premises.TranslationAgreesV1.ProjRegsEq initial.regs other.regs ∧
      WritesOnly (rowsFootprint spec.imageRows).byte (fun a => initial.mem[a]?) (fun a => other.mem[a]?) ∧
      (∀ physical : Nat, (other.mem[physical]?).isSome = (initial.mem[physical]?).isSome) := by
  obtain ⟨address, fault, other, call, fields⟩ :=
    native_full_translate_total spec config rows mapping query member query.request.aligned data.leafLevel
      data.logical data.physical data.view data.path data.permissions initial data.lower current.host mode
      current.core current.geometry access.layout current.images current.guards access.checks current.rawFault
      current.enabled data.accessEL data.nonsecure current.cache access.epd access.map access.outputPolicy
  have clean := clean_translate_fields_to_clean fields
  have preserved := current_s1_after data current access clean
  have frames := clean_translate_image_frame clean
  have modeAfter : HostEL0ModeAt other.regs := by
    obtain ⟨params, out, operations, active, format, faultEq, faultNone, mapResult, va, normal,
      addressFault, nonsecure, pa, registers, history, images, held⟩ := fields
    exact (translate_current_host_mode config spec.controls spec.physicalConfig query.request.raw
      (translateCurrent out) initial other current.host mode registers).2
  exact ⟨address, fault, other, call, fields, preserved.1, preserved.2, modeAfter, frames.2⟩

#print axioms host_el0_mode_register_fields
#print axioms current_full_translate_total
end ArmCert.Translate.Model
