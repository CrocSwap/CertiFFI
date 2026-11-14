-- (iii) groundwork: the canonical-invariant translation (
-- current_translate_address_total) together with the ORDERED actual translation traffic, no-update
-- conditional, cached WB and static slots from native_translate_address_events_total, on the SAME
-- actual call (deterministic result).
import ArmCertWalk.NativeTranslateAddressEvents
import ArmCertTranslateModel.TranslateAddressBinding
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

theorem current_translate_address_events {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
      (∀ physical : Nat, (other.mem[physical]?).isSome = (initial.mem[physical]?).isSome) ∧
      ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
        (leaf : Nat × Bool × Array Event) (middle : Array Event),
        walk.length = data.leafLevel + 1 - spec.layout.start ∧
        TranslateTrafficFrom (initial.events.push (.translationStart info)) walk leaf middle ∧
        other.events = middle.push (.translationEnd address) ∧
        (RawImageAt spec.imageRows initial.mem →
          NoUpdateRows {spec.params with haft := hostHAFT initial.regs} query.request.raw spec.imageRows = true →
          (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧ other.mem = initial.mem) ∧
        (outputCached query.request.raw initial.regs = true →
          address.memattrs.inner.attrs = MemAttr_WB ∧ address.memattrs.outer.attrs = MemAttr_WB) ∧
        ((spec.logicalRows.map (·.logical)).Nodup →
          walk.map (·.1) = declaredSlots spec.logicalRows spec.layout query.va) := by
  obtain ⟨address, fault, other, call, fields, currentO, accessO, modeO, debugO, aa64O, speO, proj, writes, present⟩ :=
    current_translate_address_total spec config rows mapping query member data initial current access mode aa64 debug spe
  obtain ⟨address', fault', other', call', _, info, walk, leaf, middle, walkLen, traffic, events, cond, _, wb, slots⟩ :=
    native_translate_address_events_total spec config rows mapping query member query.request.aligned query.size
      data.leafLevel data.logical data.physical data.view data.path data.permissions initial data.lower
      current.host mode aa64 debug spe current.core current.geometry access.layout current.images
      current.guards access.checks current.rawFault current.enabled data.accessEL data.nonsecure current.cache
      access.epd access.map access.outputPolicy
  rw [call] at call'
  simp only [EStateM.Result.ok.injEq] at call'
  obtain ⟨rfl, rfl⟩ := call'
  exact ⟨address, fault, other, call, fields, currentO, accessO, modeO, debugO, aa64O, speO, proj, writes, present,
    info, walk, leaf, middle, walkLen, traffic, events, cond, wb, slots⟩

#print axioms current_translate_address_events
end ArmCertWalk
