import ReleaseProfile.GB10.Canonical

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024

namespace ReleaseProfile.GB10

/-- Exactly the nine worked normal-entry equations; FPCR/FPSR and other PSTATE values remain free. -/
structure NormalCallerDomain (caller : Caller) : Prop where
  el : caller.pstate.EL = 0#2
  nrw : caller.pstate.nRW = 0#1
  alignment : caller.pstate.A = 0#1
  irq : caller.pstate.I = 0#1
  fiq : caller.pstate.F = 0#1
  illegal : caller.pstate.IL = 0#1
  singleStep : caller.pstate.SS = 0#1
  branchType : caller.pstate.BTYPE = 0#2
  tagCheckOverride : caller.pstate.TCO = 0#1

#check "CURRENT_DECL GB10.callerDomainWitness"
/-- Only a mathematical domain-inhabitation example; never the caller selected for an invocation. -/
private def callerDomainWitness : Caller where
  pstate := {
    N := 0
    Z := 0
    C := 0
    V := 0
    D := 0
    A := 0
    I := 0
    F := 0
    EXLOCK := 0
    PAN := 0
    UAO := 0
    DIT := 0
    TCO := 0
    PM := 0
    PPEND := 0
    BTYPE := 0
    ZA := 0
    SM := 0
    ALLINT := 0
    SS := 0
    IL := 0
    EL := 0
    nRW := 0
    SP := 0
    Q := 0
    GE := 0
    SSBS := 0
    IT := 0
    J := 0
    T := 0
    E := 0
    M := 0
  }
  fpcr := 0
  fpsr := 0

theorem normalCallerDomain_nonempty : ∃ caller : Caller, NormalCallerDomain caller := by
  refine ⟨callerDomainWitness, ?_⟩
  constructor <;> rfl

/-- The two entry callers are independent. Shared-context agreement is a separate source projection. -/
structure CTCallerDomain (unknowns : Unknowns) (caller1 caller2 : Caller) : Prop where
  first : NormalCallerDomain caller1
  second : NormalCallerDomain caller2
  context : commonView unknowns caller1 = commonView unknowns caller2

theorem ctCallerDomain_of_normal (unknowns : Unknowns) (caller1 caller2 : Caller)
    (first : NormalCallerDomain caller1) (second : NormalCallerDomain caller2) :
    CTCallerDomain unknowns caller1 caller2 :=
  ⟨first, second, commonView_exact unknowns caller1 caller2⟩

theorem ctCallerDomain_nonempty (unknowns : Unknowns) :
    ∃ caller1 caller2 : Caller, CTCallerDomain unknowns caller1 caller2 := by
  obtain ⟨caller, normal⟩ := normalCallerDomain_nonempty
  exact ⟨caller, caller, ctCallerDomain_of_normal unknowns caller caller normal normal⟩

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.normalCallerDomain_nonempty
#print axioms ReleaseProfile.GB10.ctCallerDomain_nonempty
#print axioms ReleaseProfile.GB10.ctCallerDomain_of_normal
