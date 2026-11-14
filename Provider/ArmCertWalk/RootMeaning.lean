import ArmCertWalk.RootBaseSource
import Pilot.ObservationSimp

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Source geometry with the selected 4 KiB, 64-bit descriptor format. The
input-size field remains actual data; this is not a fixed four-level root. -/
def rootStartLevel (params : S1TTWParams) : Int :=
  3 - fdiv_int ((AArch64_IASize params.txsz - 1) - 12) 9

def rootTableSize (params : S1TTWParams) : Int :=
  (AArch64_IASize params.txsz - ((3 - rootStartLevel params) * 9 + 12)) + 3

def rootBaseValue (params : S1TTWParams) (ttbr : BitVec 128) : BitVec 56 :=
  Align_bits (Sail.BitVec.updateSubrange (0#56) 47 1 (Sail.BitVec.extractLsb ttbr 47 1))
    (_shl_int_general 1 (rootTableSize params))

theorem root_start_level_eq (params : S1TTWParams) (d128 : params.d128 = 0#1)
    (tg : params.tgx = .TGx_4KB) :
    AArch64_S1StartLevel params = rootStartLevel params := by
  simp [AArch64_S1StartLevel, rootStartLevel, d128, tg, TGxGranuleBits, FINAL_LEVEL]

def RootBaseEffect (expected : BitVec 56) (state : State) :
    EStateM.Result (Sail.Error exception) State (BitVec 56) → Prop
  | .ok actual other => actual = expected ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem root_base_effect (params : S1TTWParams) (ttbr : BitVec 128) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB) :
    RootBaseEffect (rootBaseValue params ttbr) state
      (AArch64_S1TTBaseAddress params .Regime_EL20 ttbr state) := by
  rw [RootBaseSource.complete params ttbr state d128 ds tg]
  observe_simp [RootBaseEffect, rootBaseValue, rootTableSize, rootStartLevel, RootBaseSource.native]
  rw [root_start_level_eq params d128 tg]
  rfl

theorem root_base_total (params : S1TTWParams) (ttbr : BitVec 128) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB) :
    ∃ other, AArch64_S1TTBaseAddress params .Regime_EL20 ttbr state =
      .ok (rootBaseValue params ttbr) other ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have effect := root_base_effect params ttbr state d128 ds tg
  cases actual : AArch64_S1TTBaseAddress params .Regime_EL20 ttbr state with
  | error err other => simp only [actual, RootBaseEffect] at effect
  | ok answer other =>
    have detail := by simpa only [actual, RootBaseEffect] using effect
    exact ⟨other, by rw [← detail.1], detail.2⟩

#print axioms root_start_level_eq
#print axioms root_base_effect
#print axioms root_base_total

end ArmCertWalk
