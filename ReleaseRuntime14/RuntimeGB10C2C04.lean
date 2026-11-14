import RuntimeGB10C04
import ReleaseProfile.GB10.ModelEntry
import ReleaseProfile.GB10.SpecWitness

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-! Runtime c04 full/fullpc positive C2 targets and reductions (generated; normal_c2_reduce pattern). -/

namespace ReleaseProfile.GB10.Runtime

open ReleaseProfile.MachineSource ReleaseProfile.GB10

def FullC2_c04 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Prop :=
  ∃ (domain : ArmCert.Translate.Model.QueryDomain) (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat) (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (entry : ArmBridge.Draft.NativeState),
    AgreesAt (Configuration.ofSource rho caller) entry.regs ∧ SourceSpec rho caller spec ∧
    FullResidual_c04 spec rows mapping table sc bytes base ifunc p budget inputs rho caller entry

theorem full_c2_reduce_c04 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (sem : ModelSemantics) (payloadOf : BitVec 88 → ModelPayload)
    (disabled : ∀ pcount, TimersDisabled (payloadOf pcount).data.timers)
    {domain : ArmCert.Translate.Model.QueryDomain} (tables : TopologyTables domain) (oracle : OracleChoice)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat) (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64))
    (residual : ∀ (pcount : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec domain),
      SourceSpec rho caller spec →
      spec.layout = tables.layout → spec.logicalRows = tables.logicalRows →
      spec.imageRows = tables.imageRows →
      TimersQuiet (makeModelEntry sem rho caller (payloadOf pcount)).regs budget →
      FullResidual_c04 spec rows mapping table sc bytes base ifunc p budget inputs rho caller
        (makeModelEntry sem rho caller (payloadOf pcount))) :
    FullC2_c04 rho caller := by
  obtain ⟨pcount, -⟩ : ∃ _ : BitVec 88, True := ⟨0#88, trivial⟩
  have timers := model_timersQuiet sem rho caller (payloadOf pcount) (disabled pcount) budget
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho caller tables oracle (payloadOf pcount).data
    (makeModelEntry sem rho caller (payloadOf pcount)) rfl
  exact ⟨domain, spec, rows, mapping, table, sc, bytes, base, ifunc, p, budget, inputs,
    makeModelEntry sem rho caller (payloadOf pcount), makeModelEntry_agrees sem rho caller (payloadOf pcount),
    sspec, residual pcount spec sspec hl hlr hir timers⟩

def FullPCC2_c04 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Prop :=
  ∃ (domain : ArmCert.Translate.Model.QueryDomain) (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat) (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (entry : ArmBridge.Draft.NativeState),
    AgreesAt (Configuration.ofSource rho caller) entry.regs ∧ SourceSpec rho caller spec ∧
    FullPCResidual_c04 spec rows mapping table sc bytes base ifunc p budget inputs rho caller entry

theorem fullpc_c2_reduce_c04 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (sem : ModelSemantics) (payloadOf : BitVec 88 → ModelPayload)
    (disabled : ∀ pcount, TimersDisabled (payloadOf pcount).data.timers)
    {domain : ArmCert.Translate.Model.QueryDomain} (tables : TopologyTables domain) (oracle : OracleChoice)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat) (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64))
    (residual : ∀ (pcount : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec domain),
      SourceSpec rho caller spec →
      spec.layout = tables.layout → spec.logicalRows = tables.logicalRows →
      spec.imageRows = tables.imageRows →
      TimersQuiet (makeModelEntry sem rho caller (payloadOf pcount)).regs budget →
      FullPCResidual_c04 spec rows mapping table sc bytes base ifunc p budget inputs rho caller
        (makeModelEntry sem rho caller (payloadOf pcount))) :
    FullPCC2_c04 rho caller := by
  obtain ⟨pcount, -⟩ : ∃ _ : BitVec 88, True := ⟨0#88, trivial⟩
  have timers := model_timersQuiet sem rho caller (payloadOf pcount) (disabled pcount) budget
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho caller tables oracle (payloadOf pcount).data
    (makeModelEntry sem rho caller (payloadOf pcount)) rfl
  exact ⟨domain, spec, rows, mapping, table, sc, bytes, base, ifunc, p, budget, inputs,
    makeModelEntry sem rho caller (payloadOf pcount), makeModelEntry_agrees sem rho caller (payloadOf pcount),
    sspec, residual pcount spec sspec hl hlr hir timers⟩

end ReleaseProfile.GB10.Runtime

#print axioms ReleaseProfile.GB10.Runtime.full_c2_reduce_c04
#print axioms ReleaseProfile.GB10.Runtime.fullpc_c2_reduce_c04
