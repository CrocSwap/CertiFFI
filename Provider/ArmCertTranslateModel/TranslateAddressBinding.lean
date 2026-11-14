import ArmCertTranslateModel.IfetchTranslateBinding
import ArmCertWalk.NativeTranslateAddressTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Derive the ORIGINAL actual `AArch64_TranslateAddress` call for ANY declared
    query (data or instruction fetch) with the query's actual raw descriptor,
    alignment AND size. Existing E11 (MDE/HDE and SPESampleInFlight) and
    FeatureImpl[4] (catalogue F6/E1) remain explicit current producer links on
    the ORIGINAL state; every returned fact concerns the SAME actual successor,
    covering both guarded-page register cases. No access class is excluded and
    no call answer is supplied. Physical read/fetch and the closed certified-run
    join remain open. -/
theorem current_translate_address_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (data : S1AccessData spec config rows query)
    (initial : State) (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (mode : HostEL0ModeAt initial.regs)
    (aa64 : initial.regs.FeatureImpl[4] = true) (debug : ExistingE11DebugAt initial.regs)
    (spe : initial.regs.bank_Bool .SPESampleInFlight = false) :
    ∃ address fault other,
      AArch64_TranslateAddress query.va query.request.raw query.request.aligned query.size initial =
        .ok address other ∧
      CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial (fault, address) other ∧
      CurrentS1At spec config rows other ∧ CurrentS1AccessAt spec config rows mapping query data other ∧
      HostEL0ModeAt other.regs ∧ ExistingE11DebugAt other.regs ∧ other.regs.FeatureImpl[4] = true ∧
      other.regs.bank_Bool .SPESampleInFlight = false ∧
      ArmCert.Premises.TranslationAgreesV1.ProjRegsEq initial.regs other.regs ∧
      WritesOnly (rowsFootprint spec.imageRows).byte (fun a => initial.mem[a]?) (fun a => other.mem[a]?) ∧
      (∀ physical : Nat, (other.mem[physical]?).isSome = (initial.mem[physical]?).isSome) := by
  obtain ⟨address, fault, other, call, fields⟩ :=
    native_translate_address_total spec config rows mapping query member query.request.aligned query.size
      data.leafLevel data.logical data.physical data.view data.path data.permissions initial data.lower
      current.host mode aa64 debug spe current.core current.geometry access.layout current.images
      current.guards access.checks current.rawFault current.enabled data.accessEL data.nonsecure current.cache
      access.epd access.map access.outputPolicy
  have clean := clean_translate_fields_to_clean fields
  have preserved := current_s1_after data current access clean
  have frames := clean_translate_image_frame clean
  have controls : HostEL0ModeAt other.regs ∧ ExistingE11DebugAt other.regs ∧
      other.regs.FeatureImpl[4] = true ∧ other.regs.bank_Bool .SPESampleInFlight = false := by
    obtain ⟨params, out, operations, active, format, faultEq, faultNone, mapResult, va, normal,
      addressFault, nonsecure, pa, registers, history, images, held⟩ := fields
    refine ⟨(translate_current_host_mode config spec.controls spec.physicalConfig query.request.raw
      (translateCurrent out) initial other current.host mode registers).2, ?_, ?_, ?_⟩
    · rw [registers]
      unfold fetchGuardRegs
      split
      · exact ExistingE11DebugAt.guarded_page initial.regs debug _
      · exact debug
    · rw [registers]
      unfold fetchGuardRegs
      split <;> exact aa64
    · rw [registers]
      unfold fetchGuardRegs
      split <;> exact spe
  exact ⟨address, fault, other, call, fields, preserved.1, preserved.2,
    controls.1, controls.2.1, controls.2.2.1, controls.2.2.2, frames.2⟩

#print axioms current_translate_address_total
end ArmCert.Translate.Model
