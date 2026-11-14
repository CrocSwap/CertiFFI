-- Fetch inputs bound to the canonical query invariant (CurrentS1At/CurrentS1AccessAt,
-- current-address 2620bf10) at the ACTUAL beforeFetch state s. The fetch wrapper's own two
-- register writes (BTypeCompatible, __InstructionStep) are transported with
-- register-field lemmas; no walk input is supplied at the internal pre-read state.
import ArmCertWalk.NativeFetchTotal
import ArmCertTranslateModel.TranslateAddressBinding
import ArmCertTranslateModel.CurrentProgramTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
open ArmCert.Eval.M1a.Fetch2

/-- The state the actual fetch wrapper reads memory from (same memory). -/
def fetchPre (s : State) : State := {s with regs := fetchRegs s.regs}

theorem fetchRegs_bool_ne (r : Regs) (k : Bank_Bool) (ne : k ≠ .__InstructionStep) :
    (fetchRegs r).bank_Bool k = r.bank_Bool k := by
  show RegMap.set r.bank_Bool .__InstructionStep false k = r.bank_Bool k
  exact RegMap.set_ne _ _ ne

theorem current_s1_fetchPre {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {s : State}
    (current : CurrentS1At spec config rows s) : CurrentS1At spec config rows (fetchPre s) where
  images := ⟨current.images.covered, current.images.topology, current.images.attributes,
    current.images.writeback, current.images.permissions.registers _ rfl (fun _ => rfl)⟩
  host := current.host.registers rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
  core := host_image_core_register_fields current.core rfl rfl rfl rfl rfl
  geometry := current.geometry.trans (normalized_txsz_register_fields _ _ rfl rfl).symm
  guards := current.guards.registers rfl rfl
  rawFault := (source_txsz_fault_register_fields _ _ _ rfl).trans current.rawFault
  enabled := current.enabled
  cache := (fetchRegs_bool_ne s.regs _ (by decide)).trans current.cache

/-- Fetch inputs at the ACTUAL beforeFetch state: canonical query invariant,
existing mode/E11/F6/SPE, and for EVERY actual IFETCH descriptor a declared
query with current access data. -/
theorem native_fetch_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (step : StepFacts s.regs) (el : s.regs.PSTATE.EL = 0#2)
    (pcLow : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) (il : s.regs.PSTATE.IL = 0#1)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc s acc → domain (queryOf acc) ∧
      ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data s) :
    ∃ acc word final address faultOut translated leafLevel view,
      ActualIFetchAcc s acc ∧
      __FetchInstr s.regs._PC s = .ok (__InstrEnc.__A64, word) final ∧
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view (fetchPre s)
        (faultOut, address) translated ∧
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
        some (word.extractLsb' (8 * i) 8)) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem ∧
      final.events = translated.events.push
        (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) := by
  have pre := current_s1_fetchPre current
  have accessPre : ∀ {query : AccessQuery} {data : S1AccessData spec config rows query},
      CurrentS1AccessAt spec config rows mapping query data s →
      CurrentS1AccessAt spec config rows mapping query data (fetchPre s) :=
    fun access => current_s1_access_registers access rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
  -- query-independent layout/EPD/VA range at the actual PC, from one actual descriptor
  obtain ⟨acc0, after0, call0, _, _⟩ :=
    MemM1.MemReadIF.createR s step.rme step.nrw step.b3 step.a3 el step.ns
  obtain ⟨_, data0, access0⟩ := perAcc acc0 ⟨s, after0, rfl, call0⟩
  have va0 := vaOf acc0
  have access0Pre := accessPre access0
  exact native_fetch_total spec config rows mapping s step el pcLow il queryOf rawOf vaOf
    (fetchPre s) rfl rfl (va0 ▸ data0.lower) pre.host
    (host_el0_mode_register_fields mode rfl rfl rfl rfl) aa64
    (existing_e11_debug_register_fields debug rfl rfl)
    ((fetchRegs_bool_ne s.regs _ (by decide)).trans spe)
    pre.core pre.geometry (va0 ▸ access0Pre.layout) pre.images pre.guards pre.rawFault pre.enabled
    pre.cache (va0 ▸ access0Pre.epd) mmio present
    (fun acc actual => by
      obtain ⟨member, data, access⟩ := perAcc acc actual
      have accessP := accessPre access
      exact ⟨member, data.accessEL, data.nonsecure, accessP.checks, accessP.outputPolicy,
        data.leafLevel, data.logical, data.physical, data.view, data.path, ⟨data.permissions⟩,
        accessP.map⟩)

#print axioms native_fetch_current
end ArmCertWalk
