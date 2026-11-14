import ArmCertTranslateModel.TranslateAddressBinding
import MemReloc.Placement

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Current, checkable separation: every mapped PA of the scoped C9 image lies
    outside the physical descriptor-byte footprint. It concerns the supplied
    mapping and footprint only; it is not a future-execution premise. -/
def ImageTableSeparated (scope : Nat → Prop) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) (table : Nat → Prop) : Prop :=
  ∀ offset pa, scope offset → mapping (MemReloc.imageAddress base offset) = some pa → ¬ table pa

/-- A physical table-only write frame preserves every separated scoped image byte. -/
theorem scope_memory_eq_of_writes_only {scope : Nat → Prop} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {table : Nat → Prop} {left right : State}
    (separated : ImageTableSeparated scope base mapping table)
    (writes : WritesOnly table (fun a => left.mem[a]?) (fun a => right.mem[a]?)) :
    MemReloc.ScopeMemoryEq scope base mapping left right :=
  fun offset pa inside mapped => writes pa (separated offset pa inside mapped)

/-- C9 placement across the ORIGINAL actual `AArch64_TranslateAddress` call for
    any declared query. Placement at the original state plus image/table
    separation yields placement on the SAME actual successor, which also keeps
    every current invariant of `current_translate_address_total`. When the query
    VA is a scoped image address, the actual translated PA holds that image byte
    in the actual post-translation memory (including own AF/dirty stores).
    The mapping is the one the current invariant binds the actual walk to. -/
theorem c9_translate_address_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (data : S1AccessData spec config rows query)
    (initial : State) (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (mode : HostEL0ModeAt initial.regs)
    (aa64 : initial.regs.FeatureImpl[4] = true) (debug : ExistingE11DebugAt initial.regs)
    (spe : initial.regs.bank_Bool .SPESampleInFlight = false)
    {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word}
    (placed : MemReloc.ImageOn scope image initial base mapping)
    (separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte) :
    ∃ address fault other,
      AArch64_TranslateAddress query.va query.request.raw query.request.aligned query.size initial =
        .ok address other ∧
      CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial (fault, address) other ∧
      CurrentS1At spec config rows other ∧ CurrentS1AccessAt spec config rows mapping query data other ∧
      HostEL0ModeAt other.regs ∧ ExistingE11DebugAt other.regs ∧ other.regs.FeatureImpl[4] = true ∧
      other.regs.bank_Bool .SPESampleInFlight = false ∧
      ArmCert.Premises.TranslationAgreesV1.ProjRegsEq initial.regs other.regs ∧
      MemReloc.ImageOn scope image other base mapping ∧
      (∀ offset byte, scope offset → query.va = MemReloc.imageAddress base offset →
        image offset = some byte → other.mem[address.paddress.address.toNat]? = some byte) := by
  obtain ⟨address, fault, other, call, fields, s1, s1access, hostMode, e11, f4, speAfter, proj, writes,
    _presence⟩ :=
    current_translate_address_total spec config rows mapping query member data initial current access
      mode aa64 debug spe
  have after : MemReloc.ImageOn scope image other base mapping :=
    MemReloc.imageOn_frame placed (scope_memory_eq_of_writes_only separated writes)
  refine ⟨address, fault, other, call, fields, s1, s1access, hostMode, e11, f4, speAfter, proj, after, ?_⟩
  intro offset byte inside va value
  obtain ⟨params, out, operations, _params, _format, _faultEq, _faultNone, mapped, _rest⟩ := fields
  obtain ⟨pa, paMapped, paByte⟩ := MemReloc.imageOn_byte after inside value
  rw [← va, mapped] at paMapped
  rw [Option.some.inj paMapped]
  exact paByte

#print axioms scope_memory_eq_of_writes_only
#print axioms c9_translate_address_total
end ArmCert.Translate.Model
