-- Route 7 / C2 targets (loops): positive non-vacuity of the C1 premise sets. For every admissible completion and
-- caller there is a clean world (spec, rows, mapping, base, pointers, n, entry) in which the actual-entry agreement with
-- the canonical configuration, SourceSpec, TimersQuiet, every card row and the entry residual hold. The tag-status rows
-- are a CLAIM_CONDITION and are not discharged by C2 (card). The world itself is generated route-7 world.
import Route7Root.CT0
import Route7Root.CT0Set
import Route7Root.CT0Move
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ReleaseProfile.MachineSource ReleaseProfile.GB10
set_option autoImplicit false
set_option Elab.async false

namespace Route7Root
open ArmCertLoop ArmCertLoop.ContractDraft CertiFFI.Claim

def MemcpyC2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Prop :=
  ∃ (domain : QueryDomain) (spec : TopologyImageSpec domain) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat) (e : NativeState),
    AgreesAt (Configuration.ofSource rho caller) e.regs ∧ SourceSpec rho caller spec ∧
    TimersQuiet e.regs (Schedule.copySteps n) ∧ MemcpyRows spec mapping base d s returnPC n e ∧
    Route7Entry.EntryResidual spec rows mapping (memcpyConsumer spec mapping base d s n) codeScope image base
      (ContractDraft.offset base returnPC n) rho caller e

def MemsetC2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Prop :=
  ∃ (domain : QueryDomain) (spec : TopologyImageSpec domain) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base d fill returnPC : BitVec 64) (n : Nat) (e : NativeState),
    AgreesAt (Configuration.ofSource rho caller) e.regs ∧ SourceSpec rho caller spec ∧
    TimersQuiet e.regs (Schedule.setSteps n) ∧
    ∃ rws : MemsetRows spec mapping base d fill returnPC n e,
      Route7Entry.EntryResidual spec rows mapping (memsetConsumer spec mapping base d n) codeScope image base
        (SetNative.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e

def MemmoveC2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Prop :=
  ∃ (domain : QueryDomain) (spec : TopologyImageSpec domain) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat) (e : NativeState),
    AgreesAt (Configuration.ofSource rho caller) e.regs ∧ SourceSpec rho caller spec ∧
    TimersQuiet e.regs (Schedule.moveSteps (Route7Move.movePath d s n) n) ∧
    ∃ rws : MemmoveRows spec mapping base d s returnPC n e,
      Route7Entry.EntryResidual spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
        (Route7Move.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e

/-- Sanity (the C2 world feeds C1): a C2 world plus the claim-condition tag-status rows gives the C1 conclusion at it. -/
theorem memcpy_c1_at_c2 (real : Type) [Sail.SailReal real] (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : MemcpyC2 rho caller)
    (statusRows : ∀ (e : NativeState) (n : Nat), DeploymentObligation "loop:memcpy:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) (2 * n))) :
    ∃ (mapping : BitVec 64 → Option Nat) (d s returnPC : BitVec 64) (n : Nat) (e : NativeState),
      CopyPost mapping d s returnPC n e (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (Schedule.copySteps n)) := by
  obtain ⟨_, spec, rows, mapping, base, d, s, returnPC, n, e, ag, sspec, timers, rws, res⟩ := w
  exact ⟨mapping, d, s, returnPC, n, e,
    (memcpyFromSource real spec rows mapping base d s returnPC n rho caller (Configuration.ofSource rho caller) e ag sspec
      timers rws res (statusRows e n)).2⟩

end Route7Root
#print axioms Route7Root.memcpy_c1_at_c2
