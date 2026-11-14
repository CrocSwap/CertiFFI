import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmCert.Premises.TranslationAgreesV1

/- Projection v2: moved VERBATIM from eval transport-run v1
   (Transport.TranslationAgrees v2 684d7557) into the step-boundary-v2 lineage so the
   boundary v2 Premises can name it; same namespace and declaration names. The run form
   AlongRun stays in transport-run (it needs nrun). -/
/- a design decision, GAP-2 option M2. NAMED PREMISE, proposed for
   ArmCert premises v1.6. It is a successful-call premise about the actual
   AArch64_TranslateAddress; it carries NO F3 credit. It is to be discharged
   later by the normal-outcome refinement (M1, backlog 52, armcert-memory) plus
   table-isolation facts. Profile: decision-28/32 modeled implementation
   profile (PA48/IPS5; real GB10 PA is 40-bit, backlog 51). -/

abbrev State := SequentialState Regs oracleChoiceSource

/-- Consumer side of address translation for one certified program. -/
structure ConsumerMap where
  /-- Physical address the consumer's memory model assigns to each virtual
      address (identity on 56 bits for ArmBridge.Draft.project). -/
  pa : BitVec 64 → BitVec 56
  /-- The accesses the certified program may issue: virtual address, access
      descriptor (EL0, NonSecure, permitted read/write/exec rights), alignment
      flag and size. Certificates must prove every issued access is permitted. -/
  permitted : BitVec 64 → AccessDescriptor → Bool → Int → Prop
  /-- Bytes holding translation tables. They are never consumer-accessed and
      may receive hardware access-flag/dirty-bit writes during translation. -/
  tableByte : Nat → Prop

/-- Equality of exactly the register fields read by ArmBridge.Draft.project
    (d2a15afe): GPR0-30, SP_EL0 (GPR31), the scalable vector file (SFP = low
    128 bits), PC, NZCV and the ten projected system registers. Other register
    state (PMU/SPE counters, translation bookkeeping, ...) is unconstrained
    (defects review 7a38 item 1). -/
def ProjRegsEq (r r' : Regs) : Prop :=
  r'.gpr = r.gpr ∧ r'.SP_EL0 = r.SP_EL0 ∧ r'._Z = r._Z ∧ r'._PC = r._PC ∧
  r'.PSTATE.N = r.PSTATE.N ∧ r'.PSTATE.Z = r.PSTATE.Z ∧
  r'.PSTATE.C = r.PSTATE.C ∧ r'.PSTATE.V = r.PSTATE.V ∧
  ArmFull.Register.TPIDR_EL0.get r' = ArmFull.Register.TPIDR_EL0.get r ∧
  ArmFull.Register.TPIDRRO_EL0.get r' = ArmFull.Register.TPIDRRO_EL0.get r ∧
  ArmFull.Register.DCZID_EL0.get r' = ArmFull.Register.DCZID_EL0.get r ∧
  ArmFull.Register.MIDR_EL1.get r' = ArmFull.Register.MIDR_EL1.get r ∧
  ArmFull.Register.ID_AA64ISAR1_EL1.get r' = ArmFull.Register.ID_AA64ISAR1_EL1.get r ∧
  ArmFull.Register.ID_AA64ISAR2_EL1.get r' = ArmFull.Register.ID_AA64ISAR2_EL1.get r ∧
  ArmFull.Register.ID_AA64MMFR1_EL1.get r' = ArmFull.Register.ID_AA64MMFR1_EL1.get r ∧
  ArmFull.Register.TCR_EL1.get r' = ArmFull.Register.TCR_EL1.get r ∧
  ArmFull.Register.TCR_EL2.get r' = ArmFull.Register.TCR_EL2.get r ∧
  ArmFull.Register.HCR_EL2.get r' = ArmFull.Register.HCR_EL2.get r

theorem ProjRegsEq.refl (r : Regs) : ProjRegsEq r r :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- TranslationAgrees m s (v2): from state s, every permitted access translates
    without fault to the NonSecure physical address the consumer assigns, as
    Normal memory; the translation leaves the projected registers unchanged
    and changes memory only in table bytes (other registers, choice and event
    state are unconstrained). -/
def TranslationAgrees (m : ConsumerMap) (s : State) : Prop :=
  ∀ va accdesc aligned size, m.permitted va accdesc aligned size →
    ∃ ad t, AArch64_TranslateAddress va accdesc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := m.pa va } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      ProjRegsEq s.regs t.regs ∧
      ∀ a, ¬ m.tableByte a → t.mem[a]? = s.mem[a]?

/-- An empty permitted set makes the premise trivially true; certificates must
    prove each issued access is permitted (non-vacuity of a nonempty instance is
    the M1 deliverable, backlog 52). -/
theorem trivial_of_empty (m : ConsumerMap) (s : State)
    (h : ∀ va accdesc aligned size, ¬ m.permitted va accdesc aligned size) :
    TranslationAgrees m s := fun va accdesc aligned size hp => absurd hp (h _ _ _ _)

/-- The identity consumer map used with ArmBridge.Draft.project (LNSym byte at
    address v is the native physical byte at v.toNat). Permitted accesses must
    additionally have the top byte zero (TBI0 tags are not identity-mapped) and
    lie below 2^48 (PA48 modeled profile). -/
def identityPA (va : BitVec 64) : BitVec 56 := va.setWidth 56

theorem identityPA_toNat (va : BitVec 64) (h : va.toNat < 2 ^ 56) :
    (identityPA va).toNat = va.toNat := by
  simp [identityPA, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

#print axioms identityPA_toNat
#print axioms ProjRegsEq.refl
#print axioms trivial_of_empty
end ArmCert.Premises.TranslationAgreesV1
