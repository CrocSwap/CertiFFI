import ArmCertWalk.RootEntrySource
import ArmCertWalk.RootGeometry

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def rootEntryLow (level : Int) : Int := (3 - level) * 9 + 12
def rootEntryHigh (params : S1TTWParams) : Int := AArch64_IASize params.txsz - 1

def RootEntryBounds (params : S1TTWParams) (level : Int) : Prop :=
  0 ≤ rootEntryLow level ∧ rootEntryLow level ≤ rootEntryHigh params ∧
    rootEntryHigh params < 64 ∧ (rootEntryHigh params - rootEntryLow level + 1) + 3 ≤ 56

def rootEntryValue (params : S1TTWParams) (level : Int) (va : BitVec 64)
    (base : FullAddress) : FullAddress :=
  { address := base.address ||| Sail.BitVec.zeroExtend
      (Sail.BitVec.extractLsb va (Sail.Int.toNatChecked (rootEntryHigh params))
        (Sail.Int.toNatChecked (rootEntryLow level)) +++ Zeros (n := 3)) 56
    paspace := base.paspace }

theorem current_layout_entry_bounds (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (registers : Regs) (current : CurrentLayoutAt layout params va registers)
    (level : layout.start ≤ 3) : RootEntryBounds params (layout.start : Int) := by
  have geometry := current_root_geometry layout params va registers current level
  have input := current.inputBits
  have width := params.txsz.isLt
  change (layout.inputBits : Int) = 64 - (params.txsz.toNat : Int) at input
  unfold S1LogicalReference.rootBits at geometry
  unfold RootEntryBounds rootEntryLow rootEntryHigh
  rw [← current.inputBits]
  omega

def RootEntryEffect (expected : FullAddress) (state : State) :
    EStateM.Result (Sail.Error exception) State FullAddress → Prop
  | .ok actual other => actual = expected ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem root_entry_effect (level : Int) (params : S1TTWParams) (va : BitVec 64)
    (base : FullAddress) (state : State) (d128 : params.d128 = 0#1)
    (tg : params.tgx = .TGx_4KB) (bounds : RootEntryBounds params level) :
    RootEntryEffect (rootEntryValue params level va base) state
      (AArch64_S1SLTTEntryAddress level params va base state) := by
  rw [RootEntrySource.complete level params va base state d128 tg]
  dsimp only [RootEntryBounds, rootEntryLow, rootEntryHigh] at bounds
  rcases bounds with ⟨low, ordered, high, width⟩
  observe_simp [RootEntryEffect, rootEntryValue, rootEntryLow, rootEntryHigh, RootEntrySource.native]
  cases params
  cases d128
  cases tg
  rfl

theorem root_entry_total (level : Int) (params : S1TTWParams) (va : BitVec 64)
    (base : FullAddress) (state : State) (d128 : params.d128 = 0#1)
    (tg : params.tgx = .TGx_4KB) (bounds : RootEntryBounds params level) :
    ∃ other, AArch64_S1SLTTEntryAddress level params va base state =
      .ok (rootEntryValue params level va base) other ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have effect := root_entry_effect level params va base state d128 tg bounds
  cases actual : AArch64_S1SLTTEntryAddress level params va base state with
  | error err other => simp only [actual, RootEntryEffect] at effect
  | ok answer other =>
    have detail := by simpa only [actual, RootEntryEffect] using effect
    exact ⟨other, by rw [← detail.1], detail.2⟩

#print axioms current_layout_entry_bounds
#print axioms root_entry_effect
#print axioms root_entry_total

end ArmCertWalk
