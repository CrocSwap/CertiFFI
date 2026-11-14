import ReleaseProfile.GB10.ModelRegs
import BridgeDraft.StateProjection

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

/-!
# Source-built model entry (positive C2 building block)

`makeModelEntry` is the source-owned mathematical model entry: its register file is
`sourceRegs` at the admissible completion and caller, with the nonconfiguration data part and
memory from the payload. Oracle/choice bookkeeping is an explicit semantics parameter, never a
configuration input. The model entry agrees with the canonical configuration by construction, so
every atom produced from entry agreement in the worked boundaries holds at it.

The data part holds the 12 conservative data coordinates and the page-table roots TTBR0_EL2/TTBR1_EL2/HTTBR
; translation tables are program data in the payload memory.
A model entry is never an observed entry.
-/

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

/-- Nonconfiguration payload for a model entry. -/
structure ModelPayload where
  data : DataPart
  memory : Std.ExtHashMap Nat (BitVec 8)

/-- Registered model bookkeeping (oracle/choice state), a semantics parameter, not configuration. -/
structure ModelSemantics where
  choiceState : Sail.ConcurrencyInterfaceV1.Oracle × Nat
  choiceOcc : Std.ExtHashMap Nat Nat

#check "CURRENT_DECL GB10.makeModelEntry"
/-- The source-owned model entry. -/
def makeModelEntry (semantics : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (payload : ModelPayload) : ArmBridge.Draft.NativeState where
  regs := sourceRegs rho caller payload.data
  choiceState := semantics.choiceState
  choiceOcc := semantics.choiceOcc
  mem := payload.memory
  tags := ()
  cycleCount := 0
  sailOutput := #[]
  events := #[]

/-- The source register file agrees with the canonical configuration at every profile coordinate. -/
theorem sourceRegs_agrees (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (data : DataPart) : AgreesAt (Configuration.ofSource rho caller) (sourceRegs rho caller data) := by
  rintro ⟨c, notData⟩
  cases c
  case feature index =>
    show (Vector.ofFn (sourceFeature rho caller))[index.val]'index.isLt = _
    rw [Vector.getElem_ofFn]
    rfl
  case bank_BitVec_128 key =>
    cases key <;> first | (cases notData; done) | rfl
  case bank_BitVec_64 key =>
    by_cases h : isEntryData64 key = true
    · exact absurd (h.symm.trans notData) (by decide)
    · exact sourceBank64_ne rho caller data key (Bool.eq_false_iff.mpr h)
  all_goals first | (cases notData; done) | rfl

theorem makeModelEntry_agrees (semantics : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (payload : ModelPayload) :
    AgreesAt (Configuration.ofSource rho caller) (makeModelEntry semantics rho caller payload).regs :=
  sourceRegs_agrees rho caller payload.data

#check "CURRENT_DECL GB10.model_timersQuiet"
/-- GB10.TimersQuiet at the model entry, by construction: a payload whose timer data is disabled
(CTL.ENABLE = 0,) satisfies TimersQuiet for every budget. No source restriction is used. -/
theorem model_timersQuiet (semantics : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (payload : ModelPayload) (disabled : TimersDisabled payload.data.timers)
    (budget : Nat) : TimersQuiet (makeModelEntry semantics rho caller payload).regs budget :=
  timersQuiet_of_disabled _ (fun key hk => by
    have d := disabled key hk
    simp only [timerCtlKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact d) budget

/-- An agreeing actual entry and the model entry with its own data share the register file. -/
theorem actual_regs_eq_model (semantics : ModelSemantics) {rho : AdmissibleSourceCompletion}
    {caller : AdmissibleCaller rho} (configuration : Configuration rho caller)
    (e : ArmBridge.Draft.NativeState) (agreement : AgreesAt configuration e.regs) :
    e.regs = (makeModelEntry semantics rho caller ⟨dataOf e.regs, e.mem⟩).regs :=
  regs_eq_source configuration e.regs agreement

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.sourceRegs_agrees
#print axioms ReleaseProfile.GB10.makeModelEntry_agrees
#print axioms ReleaseProfile.GB10.actual_regs_eq_model
#print axioms ReleaseProfile.GB10.model_timersQuiet
