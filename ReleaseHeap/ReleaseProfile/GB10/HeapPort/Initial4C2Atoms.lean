import ReleaseProfile.GB10.HeapPort.TrapCommon
import ReleaseProfile.GB10.HeapPort.Initial4C2

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

/-! Heap Initial4 (TrapPath 8) positive C2 at the clean world variant x2 = 0, x3 = 0. -/

namespace ReleaseProfile.GB10.Heap.Trap.I4

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Normal ReleaseProfile.GB10.Heap.Variant ReleaseProfile.GB10.Heap.Trap

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
theorem a276 (pcount : BitVec 88) : CertiFFI.Claim.CallerContract "card:path-selector"
    (HeapV2StepCerts.ValBind.TrapPath 8 (V 0 0).pins (HeapV2StepCerts.E17General.qOf (EV rho caller 0 0 pcount))) := by
  refine ⟨?_⟩
  show _ ∧ _ ∧ _ ∧ _ ∧ (HeapV2StepCerts.RegBind.regVal (EV rho caller 0 0 pcount) (.x 2)).toNat < 32
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  simp only [HeapV2StepCerts.RegBind.regVal]
  show ((HeapWorldData.data.gpr.set 2 (0#64)).set 3 (0#64))[((2 : Fin 31) : Nat)].toNat < 32
  decide

#check "CURRENT_DECL GB10.Heap.Trap.I4.initial4_c2_of_statics"
/-- Positive C2 for the Heap Initial4 (TrapPath 8) card at every admissible completion and caller, given
the Translate static atoms at the variant world entry (x2 = 0, x3 = 0). -/
theorem initial4_c2_of_statics (statics : ∀ (pcount : BitVec 88)
      (spec : ArmCert.Translate.Model.TopologyImageSpec
        (fun q => ∃ q0 ∈ HeapWorldTables.queries, ArmCertWalk.SamePage q0.va q.va)),
      SourceSpec rho caller spec → spec.layout = HeapWorldTables.tables.layout →
      spec.logicalRows = HeapWorldTables.tables.logicalRows →
      spec.imageRows = HeapWorldTables.tables.imageRows → TrapStaticsAt rho caller 0 0 pcount spec) :
    Initial4C2 rho caller :=
  initial4_c2_reduce rho caller worldSemantics (worldPayload (V 0 0)) (fun _ => rfl) HeapWorldTables.tables
    HeapWorldData.oracle (V 0 0).rows (V 0 0).mapping (V 0 0).pins (V 0 0).scope (V 0 0).image (V 0 0).loadBase
    (V 0 0).base (V 0 0).offS (V 0 0).budget trapTableRows (fun _ => timers_disabled)
    (fun pcount spec sspec hlay hlr hir timers =>
      have imgs := Variant.images rho caller 0 0 pcount sspec hir
      have st := statics pcount spec sspec hlay hlr hir
      {
        timers := timers,
        a16 := a16, a17 := a17, a18 := a18, a19 := a19,
        a20 := st.a20,
        a55 := ⟨imgs.1.covered⟩,
        a56 := ⟨imgs.1.topology⟩,
        a57 := ⟨imgs.1.attributes⟩,
        a58 := ⟨imgs.1.writeback⟩,
        a59 := ⟨imgs.1.permissions⟩,
        a121 := Variant.a121 rho caller 0 0 pcount,
        a122 := st.a122,
        a123 := st.a123,
        a210 := ⟨imgs.2⟩,
        a211 := Variant.a211 rho caller 0 0 pcount sspec hir,
        a243 := a243T rho caller 0 0 pcount,
        a244 := st.a244,
        a245 := a245, a246 := a246,
        a256 := st.a256,
        a257 := Variant.a257 rho caller 0 0 pcount,
        a258 := st.a258,
        a259 := a259,
        a261 := ⟨ReleaseProfile.GB10.CodeStaticR.ofFull (st.a261).holds⟩,
        a262 := st.a262,
        a263 := a263 0 0,
        a264 := a264b 0 0,
        a265 := Normal.a261,
        a266 := st.a266,
        a267 := Variant.a264 rho caller 0 0 pcount,
        a268 := Variant.a265 rho caller 0 0 pcount,
        a269 := st.a269,
        a270 := st.a270,
        a271 := a271 0 0,
        a272 := a272 0 0,
        a273 := a273 spec hir,
        a274 := st.a274,
        a275 := a275 spec hlr,
        a276 := a276 rho caller pcount
      })

end ReleaseProfile.GB10.Heap.Trap.I4

#print axioms ReleaseProfile.GB10.Heap.Trap.I4.initial4_c2_of_statics
