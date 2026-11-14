import ArmCertWalk.TablePermissionFacts
import Pilot.S1NextTable

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def sourceTableBase (descriptor : BitVec 64) : BitVec 56 :=
  Sail.BitVec.updateSubrange (0#56) 47 12 (Sail.BitVec.extractLsb descriptor 47 12)

def nextTablePermissions (params : S1TTWParams) (current : Permissions)
    (descriptor : BitVec 64) : Permissions :=
  if params.hpd == 0#1 && params.pie == 0#1 then
    tablePermissionValue current descriptor else current

def NextTableMeaning (params : S1TTWParams) (current : TTWState) (descriptor : BitVec 64)
    (next : TTWState) : Prop :=
  next.istable = true ∧ next.level = current.level + 1 ∧
    next.baseaddress.address = sourceTableBase descriptor ∧
    next.baseaddress.paspace = .PAS_NonSecure ∧ next.memattrs = current.memattrs ∧
    next.nG = current.nG ∧ next.disch = 0#1 ∧
    next.permissions = nextTablePermissions params current.permissions descriptor

def NextTableEffect (params : S1TTWParams) (current : TTWState) (descriptor : BitVec 64)
    (state : State) : EStateM.Result (Sail.Error exception) State TTWState → Prop
  | .ok next other => NextTableMeaning params current descriptor next ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem next_table_effect (params : S1TTWParams) (current : TTWState)
    (descriptor : BitVec 64) (s2fs1mro : Bool) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure) :
    NextTableEffect params current descriptor state
      (AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL20 params descriptor state) := by
  rw [S1NextTable.complete current s2fs1mro params descriptor state d128 ds tg]
  observe_simp [NextTableEffect, NextTableMeaning, nextTablePermissions,
    tablePermissionValue, sourceTableBase, S1NextTable.native]

theorem next_table_total (params : S1TTWParams) (current : TTWState)
    (descriptor : BitVec 64) (s2fs1mro : Bool) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure) :
    ∃ next other,
      AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL20 params descriptor state =
        .ok next other ∧ NextTableMeaning params current descriptor next ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  have effect := next_table_effect params current descriptor s2fs1mro state d128 ds tg nonsecure
  cases actual : AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL20 params descriptor state with
  | error err other => simp only [actual, NextTableEffect] at effect
  | ok next other =>
    exact ⟨next, other, rfl, by simpa only [actual, NextTableEffect] using effect⟩

#print axioms next_table_effect
#print axioms next_table_total

end ArmCertWalk
