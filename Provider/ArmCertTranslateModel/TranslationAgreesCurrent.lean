import ArmCertTranslateModel.TranslateAddressBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Closed query membership at one state: every access the consumer map permits
    is a declared query with EXACTLY that VA, raw descriptor, alignment and size,
    in the domain, with current access data at this state. Produced per reached
    state by the run join from actual class proofs; not a future-success answer. -/
def ClosedMembershipAt {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (s : State) : Prop :=
  ∀ va acc aligned size, m.permitted va acc aligned size →
    ∃ query : AccessQuery, query.va = va ∧ query.request.raw = acc ∧
      query.request.aligned = aligned ∧ query.size = size ∧ domain query ∧
      ∃ data : S1AccessData spec config rows query,
        CurrentS1AccessAt spec config rows mapping query data s

/-- Static per-program agreement of the walk mapping with the consumer map on
    permitted VAs, and coverage of the descriptor footprint by `tableByte`. -/
structure ConsumerMapAgrees {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) :
    Prop where
  pa : ∀ va acc aligned size, m.permitted va acc aligned size → mapping va = some (m.pa va).toNat
  tables : ∀ a, (rowsFootprint spec.imageRows).byte a → m.tableByte a

/-- E17 (decision-32 `TranslationAgrees`, v2) at ONE state, as a theorem from the
    current structural invariant. The run join supplies the hypotheses at each
    reached state; `ConsumerMapAgrees` is static per-program data. -/
theorem translation_agrees_of_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (s : State)
    (current : CurrentS1At spec config rows s) (mode : HostEL0ModeAt s.regs)
    (aa64 : s.regs.FeatureImpl[4] = true) (debug : ExistingE11DebugAt s.regs)
    (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (closed : ClosedMembershipAt spec config rows mapping m s)
    (agrees : ConsumerMapAgrees spec mapping m) :
    ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m s := by
  intro va acc aligned size permitted
  obtain ⟨query, hva, hraw, haligned, hsize, member, data, access⟩ :=
    closed va acc aligned size permitted
  obtain ⟨address, _fault, other, call, fields, _s1, _access, _mode, _e11, _f4, _spe, proj, writes,
    _presence⟩ :=
    current_translate_address_total spec config rows mapping query member data s current access
      mode aa64 debug spe
  obtain ⟨_params, _out, _operations, _active, _format, _faultEq, _faultNone, mapped, _va, normal,
    addressFault, nonsecure, _rest⟩ := fields
  rw [hva, hraw, haligned, hsize] at call
  rw [hva, agrees.pa va acc aligned size permitted] at mapped
  have same : address.paddress.address = m.pa va :=
    (BitVec.eq_of_toNat_eq (Option.some.inj mapped)).symm
  refine ⟨address, other, call, addressFault, ?_, normal, proj, ?_⟩
  · rw [← nonsecure, ← same]
  · intro a notTable
    exact writes a (fun inFootprint => notTable (agrees.tables a inFootprint))

/-- Along any run carrier: if the run join establishes the per-state hypotheses
    at every reached state, decision-32 `TranslationAgrees` holds at every reached
    state. This is the E17 retirement target (v2 shape, no v3 event credit). -/
theorem translation_agrees_along {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (reached : Nat → Prop)
    (stateAt : Nat → State) (agrees : ConsumerMapAgrees spec mapping m)
    (invariant : ∀ n, reached n →
      CurrentS1At spec config rows (stateAt n) ∧ HostEL0ModeAt (stateAt n).regs ∧
      (stateAt n).regs.FeatureImpl[4] = true ∧ ExistingE11DebugAt (stateAt n).regs ∧
      (stateAt n).regs.bank_Bool .SPESampleInFlight = false ∧
      ClosedMembershipAt spec config rows mapping m (stateAt n)) :
    ∀ n, reached n → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m (stateAt n) := by
  intro n hn
  obtain ⟨current, mode, aa64, debug, spe, closed⟩ := invariant n hn
  exact translation_agrees_of_current spec config rows mapping m (stateAt n) current mode aa64 debug
    spe closed agrees

#print axioms translation_agrees_of_current
#print axioms translation_agrees_along
end ArmCert.Translate.Model
