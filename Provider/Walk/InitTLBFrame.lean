import Walk.InitRegisterChunks
import Walk.InitModelPrefix
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace InitTLBFrame
abbrev State := SequentialState Regs oracleChoiceSource

theorem model_tlb (s : State) : InitBoolProbe.tlb (sail_model_init () s) = some false := by
  have hRun := congrFun InitModelPrefix.equation s
  have hObs := congrArg (@InitBoolProbe.tlb Unit) hRun
  have hTail := (InitTLBProperties.observe_bind InitModelPrefix.beforeRegisters
    (fun _ => initialize_registers ()) (fun _ => InitRegisterChunks.all_chunks) s).trans
      (InitModelPrefix.prefix_tlb s)
  exact hObs.trans hTail


theorem seed_observation (p : SailM Unit)
    (h : ∀ s : State, InitBoolProbe.tlb (p s) = some false) (oracle : Oracle) :
    InitBoolProbe.tlb (p.run ({ (default : State) with choiceState := (oracle, 0) } : State)) =
      some false := by
  exact h _

theorem initial_tlb (oracle : Oracle) :
    InitBoolProbe.tlb (ArmFull.initialState oracle) = some false := by
  exact seed_observation (sail_model_init ()) model_tlb oracle


theorem exists_of_tlb (result : EStateM.Result (Sail.Error exception) State Unit)
    (h : InitBoolProbe.tlb result = some false) :
    ∃ t, result = .ok () t ∧ t.regs.bank_Bool .__tlb_enabled = false := by
  cases result with
  | error e t => simp [InitBoolProbe.tlb] at h
  | ok a t =>
    cases a
    simp only [InitBoolProbe.tlb, Option.some.injEq] at h
    exact ⟨t, rfl, h⟩


theorem model_total (s : State) :
    ∃ t, sail_model_init () s = .ok () t ∧ t.regs.bank_Bool .__tlb_enabled = false :=
  exists_of_tlb (sail_model_init () s) (model_tlb s)


theorem initial_total (oracle : Oracle) :
    ∃ t, ArmFull.initialState oracle = .ok () t ∧
      t.regs.bank_Bool .__tlb_enabled = false :=
  exists_of_tlb (ArmFull.initialState oracle) (initial_tlb oracle)
#print axioms model_tlb
#print axioms initial_total
end InitTLBFrame
