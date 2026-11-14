import ArmCertTranslateModel.TranslationAgreesCurrent
import ArmCertTranslateModel.CurrentProgramTransport
import ArmCertWalk.NativeFetchCurrent

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- The actual fetch-guard register update changes only `InGuardedPage`, so every
    register field read by any query's current access data is unchanged. -/
theorem current_s1_access_fetch_guard {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query} {before after : State}
    (acc : AccessDescriptor) (next : TTWState)
    (access : CurrentS1AccessAt spec config rows mapping query data before)
    (registers : after.regs = fetchGuardRegs acc next before.regs) :
    CurrentS1AccessAt spec config rows mapping query data after := by
  have fields : after.regs.FeatureImpl = before.regs.FeatureImpl ∧
      after.regs.bank_BitVec_64 = before.regs.bank_BitVec_64 ∧
      after.regs.bank_BitVec_128 = before.regs.bank_BitVec_128 ∧
      after.regs.bank_Int = before.regs.bank_Int := by
    rw [registers]
    unfold fetchGuardRegs
    split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨features, banks64, banks128, ints⟩ := fields
  exact current_s1_access_registers access features (by rw [banks64]) (by rw [banks64])
    (by rw [banks128]) (by rw [banks64]) (by rw [banks128]) (fun _ _ => by rw [ints])

/-- Any query's current access data survives ANY actual clean translation (of
    possibly another query): only the fetch-guard bit changes in the registers. -/
theorem current_s1_access_after_translate {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query other : AccessQuery} {data : S1AccessData spec config rows other}
    {leafLevel : Nat} {view : S1DescriptorPIE.View 64} {initial translated : State}
    {result : FaultRecord × AddressDescriptor}
    (fields : CleanTranslateResultFields spec config rows mapping query leafLevel view initial result
      translated)
    (access : CurrentS1AccessAt spec config rows mapping other data initial) :
    CurrentS1AccessAt spec config rows mapping other data translated := by
  obtain ⟨_params, out, _operations, _p, _f, _fe, _fn, _m, _va, _n, _af, _ns, _pa, registers, _rest⟩ :=
    fields
  exact current_s1_access_fetch_guard _ _ access registers

/-- Closed membership survives any actual clean translation. -/
theorem closed_membership_after_translate {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {query : AccessQuery} {leafLevel : Nat}
    {view : S1DescriptorPIE.View 64} {initial translated : State} {result : FaultRecord × AddressDescriptor}
    (closed : ClosedMembershipAt spec config rows mapping m initial)
    (fields : CleanTranslateResultFields spec config rows mapping query leafLevel view initial result
      translated) :
    ClosedMembershipAt spec config rows mapping m translated := by
  intro va acc aligned size permitted
  obtain ⟨other, hva, hraw, haligned, hsize, member, data, access⟩ := closed va acc aligned size permitted
  exact ⟨other, hva, hraw, haligned, hsize, member, data, current_s1_access_after_translate fields access⟩

/-- Closed membership depends only on registers. -/
theorem closed_membership_of_regs {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {before after : State}
    (closed : ClosedMembershipAt spec config rows mapping m before) (registers : after.regs = before.regs) :
    ClosedMembershipAt spec config rows mapping m after := by
  intro va acc aligned size permitted
  obtain ⟨other, hva, hraw, haligned, hsize, member, data, access⟩ := closed va acc aligned size permitted
  exact ⟨other, hva, hraw, haligned, hsize, member, data, access.of_regs registers⟩

/-- The fetch wrapper's own register writes keep closed membership. -/
theorem closed_membership_fetch_pre {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {s : State}
    (closed : ClosedMembershipAt spec config rows mapping m s) :
    ClosedMembershipAt spec config rows mapping m (fetchPre s) := by
  intro va acc aligned size permitted
  obtain ⟨other, hva, hraw, haligned, hsize, member, data, access⟩ := closed va acc aligned size permitted
  exact ⟨other, hva, hraw, haligned, hsize, member, data,
    current_s1_access_registers access rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)⟩

/-- One actual memory access step (Memory's DATA read8/read1/write or the fetch's
    MemSingle read): from closed membership before the translation, through the
    actual clean translation, to the access's final state whose registers are the
    translated ones. Memory contents are irrelevant to closed membership. -/
theorem closed_membership_after_access {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {query : AccessQuery} {leafLevel : Nat}
    {view : S1DescriptorPIE.View 64} {initial translated final : State}
    {result : FaultRecord × AddressDescriptor}
    (closed : ClosedMembershipAt spec config rows mapping m initial)
    (fields : CleanTranslateResultFields spec config rows mapping query leafLevel view initial result
      translated)
    (finalRegs : final.regs = translated.regs) :
    ClosedMembershipAt spec config rows mapping m final :=
  closed_membership_of_regs (closed_membership_after_translate closed fields) finalRegs

/-- The actual fetch: closed membership at the before-fetch state carries to the
    fetch's final state (fetchPre writes, translation, final regs). -/
theorem closed_membership_after_fetch {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {query : AccessQuery} {leafLevel : Nat}
    {view : S1DescriptorPIE.View 64} {s translated final : State} {result : FaultRecord × AddressDescriptor}
    (closed : ClosedMembershipAt spec config rows mapping m s)
    (fields : CleanTranslateResultFields spec config rows mapping query leafLevel view (fetchPre s) result
      translated)
    (finalRegs : final.regs = translated.regs) :
    ClosedMembershipAt spec config rows mapping m final :=
  closed_membership_after_access (closed_membership_fetch_pre closed) fields finalRegs

#print axioms current_s1_access_fetch_guard
#print axioms current_s1_access_after_translate
#print axioms closed_membership_after_translate
#print axioms closed_membership_of_regs
#print axioms closed_membership_fetch_pre
#print axioms closed_membership_after_access
#print axioms closed_membership_after_fetch
end ArmCert.Translate.Model
