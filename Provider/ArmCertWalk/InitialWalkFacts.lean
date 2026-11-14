import ArmCertWalk.InitialWalkSource
import ArmCertWalk.RootMeaning
import ArmCertWalk.PermissionProjection

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- The model's actual TTBR0 read overlays its HTTBR alias, which is distinct
from simply reading the raw 128-bit register bank. -/
def currentTTBR0 (registers : Regs) : BitVec 128 :=
  Sail.BitVec.updateSubrange (registers.bank_BitVec_128 ._TTBR0_EL2) 47 1
    (BitVec.slice (registers.bank_BitVec_64 .HTTBR) 1 47)

def selectedRootTTBR (registers : Regs) (va : BitVec 64) : BitVec 128 :=
  if AArch64_GetVARange va == .VARange_LOWER then currentTTBR0 registers
  else registers.bank_BitVec_128 .TTBR1_EL2

def InitialWalkMeaning (params : S1TTWParams) (va : BitVec 64) (registers : Regs)
    (walkstate : TTWState) : Prop :=
  walkstate.baseaddress.address = rootBaseValue params (selectedRootTTBR registers va) ∧
    walkstate.baseaddress.paspace = .PAS_NonSecure ∧ walkstate.level = rootStartLevel params ∧
    walkstate.istable = true ∧ walkstate.nG = 1#1 ∧ walkstate.disch = params.disch ∧
    walkstate.s1assured = (params.pnch == 1#1) ∧
    nativeTablePermissionProjection walkstate.permissions = ⟨0#2, false, false⟩

def InitialWalkEffect (params : S1TTWParams) (va : BitVec 64) (state : State) :
    EStateM.Result (Sail.Error exception) State TTWState → Prop
  | .ok walkstate other => InitialWalkMeaning params va state.regs walkstate ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem initial_walk_effect (params : S1TTWParams) (va : BitVec 64) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB) :
    InitialWalkEffect params va state
      (AArch64_S1InitialTTWState params va .Regime_EL20 .SS_NonSecure state) := by
  rw [InitialWalkSource.complete params va state d128 ds tg]
  observe_simp [InitialWalkEffect, InitialWalkMeaning, nativeTablePermissionProjection,
    rootBaseValue, rootTableSize, rootStartLevel, selectedRootTTBR, currentTTBR0,
    InitialWalkSource.native]
  simp only [root_start_level_eq params d128 tg, rootStartLevel]
  have pnch : (params.pnch == 1#1) = decide (params.pnch = 1#1) := by
    by_cases equal : params.pnch = 1#1 <;> simp [equal]
  simp [Sail.BitVec.zeroExtend, pnch]

theorem initial_walk_total (params : S1TTWParams) (va : BitVec 64) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB) :
    ∃ walkstate other,
      AArch64_S1InitialTTWState params va .Regime_EL20 .SS_NonSecure state =
        .ok walkstate other ∧ InitialWalkMeaning params va state.regs walkstate ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  have effect := initial_walk_effect params va state d128 ds tg
  cases actual : AArch64_S1InitialTTWState params va .Regime_EL20 .SS_NonSecure state with
  | error err other => simp only [actual, InitialWalkEffect] at effect
  | ok walkstate other =>
    exact ⟨walkstate, other, rfl, by simpa only [actual, InitialWalkEffect] using effect⟩

#print axioms initial_walk_effect
#print axioms initial_walk_total

end ArmCertWalk
