import Pilot.S1NextTable
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1NextTableFacts
abbrev State := SequentialState Regs oracleChoiceSource
def level (r : EStateM.Result (Sail.Error exception) State TTWState) : Option Int :=
  match r with
  | .ok next _ => some next.level
  | .error _ _ => none

theorem native_level (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (descriptor : BitVec 64) (s : State) :
    level (S1NextTable.native current s2fs1mro wp descriptor s) =
      some (current.level + 1) := by
  observe_simp [level, S1NextTable.native]

theorem model_returns (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (descriptor : BitVec 64) (s : State)
    (hd128 : wp.d128 = 0#1) (hds : wp.ds = 0#1) (htg : wp.tgx = .TGx_4KB) :
    ∃ next t, AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL20 wp descriptor s =
      .ok next t ∧ next.level = current.level + 1 := by
  rw [S1NextTable.complete current s2fs1mro wp descriptor s hd128 hds htg]
  have h := native_level current s2fs1mro wp descriptor s
  cases hr : S1NextTable.native current s2fs1mro wp descriptor s with
  | error e t => simp [hr, level] at h
  | ok next t =>
    exact ⟨next, t, rfl, by simpa [hr, level] using h⟩

def frame (s : State) (r : EStateM.Result (Sail.Error exception) State TTWState) : Prop :=
  match r with
  | .ok _ t => t.regs = s.regs ∧ t.mem = s.mem
  | .error _ _ => False

theorem native_frame (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (descriptor : BitVec 64) (s : State) :
    frame s (S1NextTable.native current s2fs1mro wp descriptor s) := by
  observe_simp [frame, S1NextTable.native]

#print axioms native_level
#print axioms model_returns
#print axioms native_frame
end S1NextTableFacts
