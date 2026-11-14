import ArmFull

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions

set_option maxHeartbeats 150000
set_option autoImplicit false

namespace ArmCertWalk

abbrev State := SequentialState Regs oracleChoiceSource

/-- The exact implementation-size assertion in the canonical PAMax source. -/
def LegalPAMax (bits : Int) : Prop :=
  bits = 32 ∨ bits = 36 ∨ bits = 40 ∨ bits = 42 ∨ bits = 44 ∨ bits = 48 ∨
    bits = 52 ∨ bits = 56

structure PhysicalConfig where
  paMax : Int
  ips : BitVec 3
  lpa : Bool
  lpa2 : Bool
  deriving DecidableEq, Repr

/-- A current implementation binding, without a future-call result. IPS is the
explicit helper argument; the parameter-getter layer binds it to actual TCR. -/
structure PhysicalAt (config : PhysicalConfig) (state : State) : Prop where
  legal : LegalPAMax config.paMax
  pa : state.regs.bank_Int .__supported_pa_size = config.paMax
  lpa : state.regs.FeatureImpl[69] = config.lpa
  lpa2 : state.regs.FeatureImpl[156] = config.lpa2

/-- All bit-vector inputs have a source interpretation. Raw TCR encoding
admission is a separate architectural/profile obligation. -/
def encodedBits (ips : BitVec 3) : Int :=
  if ips = 0#3 then 32 else
  if ips = 1#3 then 36 else
  if ips = 2#3 then 40 else
  if ips = 3#3 then 42 else
  if ips = 4#3 then 44 else
  if ips = 5#3 then 48 else
  if ips = 6#3 then 52 else 56

/-- Format cap in the actual 4-KiB, =0 helper. -/
def formatCap (lpa lpa2 : Bool) : Int := if lpa2 && lpa then 52 else 48

def effectiveBits (config : PhysicalConfig) : Int :=
  min (encodedBits config.ips) (min (formatCap config.lpa config.lpa2) config.paMax)

theorem encodedBits_bounds (ips : BitVec 3) :
    32 ≤ encodedBits ips ∧ encodedBits ips ≤ 56 := by
  unfold encodedBits
  repeat' first | split | omega

theorem formatCap_bounds (lpa lpa2 : Bool) :
    48 ≤ formatCap lpa lpa2 ∧ formatCap lpa lpa2 ≤ 52 := by
  cases lpa <;> cases lpa2 <;> decide

theorem legalPAMax_bounds {bits : Int} (legal : LegalPAMax bits) :
    32 ≤ bits ∧ bits ≤ 56 := by
  unfold LegalPAMax at legal
  omega

theorem effectiveBits_bounds (config : PhysicalConfig) (legal : LegalPAMax config.paMax) :
    32 ≤ effectiveBits config ∧ effectiveBits config ≤ 52 := by
  have he := encodedBits_bounds config.ips
  have hf := formatCap_bounds config.lpa config.lpa2
  have hp := legalPAMax_bounds legal
  unfold effectiveBits
  simp only [Int.min_def]
  split <;> split <;> omega

theorem PhysicalAt.of_regs {config : PhysicalConfig} {state other : State}
    (atState : PhysicalAt config state) (registers : other.regs = state.regs) :
    PhysicalAt config other := by
  exact ⟨atState.legal, by rw [registers]; exact atState.pa,
    by rw [registers]; exact atState.lpa, by rw [registers]; exact atState.lpa2⟩

theorem lpa_feature_index : num_of_Feature .FEAT_LPA = 69 := by decide
theorem lpa2_feature_index : num_of_Feature .FEAT_LPA2 = 156 := by decide

#print axioms encodedBits_bounds
#print axioms formatCap_bounds
#print axioms legalPAMax_bounds
#print axioms effectiveBits_bounds
#print axioms PhysicalAt.of_regs
#print axioms lpa_feature_index
#print axioms lpa2_feature_index

end ArmCertWalk
