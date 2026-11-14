import ArmCertWalk.TranslateOutputFinish

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def currentICache (regs : Regs) : Bool := _get_SCTLR_EL2_Type_I (regs.bank_BitVec_64 .SCTLR_EL2) == 1#1
def currentDCache (regs : Regs) : Bool := _get_SCTLR_EL2_Type_C (regs.bank_BitVec_64 .SCTLR_EL2) == 1#1

theorem icache_el20_eq (state : State) :
    AArch64_S1ICacheEnabled .Regime_EL20 state = .ok (currentICache state.regs) state := rfl

theorem dcache_el20_eq (state : State) :
    AArch64_S1DCacheEnabled .Regime_EL20 state = .ok (currentDCache state.regs) state := rfl

def instructionOutputNC (acc : AccessDescriptor) (regs : Regs) : Bool :=
  if acc.acctype == .AccessType_IFETCH then !currentICache regs else false

/-- Pure CURRENT cache fields sufficient for the source Normal-memory LS64
exclusive guard. Ordinary source metadata discharges it without pinning either
cache field; LS64 retains the actual source NC requirement. -/
def OutputCacheAdmissible (acc : AccessDescriptor) (regs : Regs) : Prop :=
  acc.ls64 = true → if acc.acctype == .AccessType_IFETCH then currentICache regs = false else currentDCache regs = false

instance outputCacheDecidable (acc : AccessDescriptor) (regs : Regs) : Decidable (OutputCacheAdmissible acc regs) := by
  unfold OutputCacheAdmissible
  infer_instance

def checkOutputCache (acc : AccessDescriptor) (regs : Regs) : Bool := decide (OutputCacheAdmissible acc regs)

theorem check_output_cache_sound (acc : AccessDescriptor) (regs : Regs)
    (checked : checkOutputCache acc regs = true) : OutputCacheAdmissible acc regs := of_decide_eq_true checked

theorem output_cache_ordinary (acc : AccessDescriptor) (regs : Regs) (ordinary : acc.ls64 = false) :
    OutputCacheAdmissible acc regs := by
  intro active
  rw [ordinary] at active
  cases active

def NormalNCFields (attrs : MemoryAttributes) : Prop :=
  attrs.memtype = .MemType_Normal ∧ attrs.inner.attrs = MemAttr_NC ∧ attrs.outer.attrs = MemAttr_NC

theorem normal_nc_fields_total (state : State) :
    ∃ attrs other, NormalNCMemAttr () state = .ok attrs other ∧ NormalNCFields attrs ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  rw [S1EntryCalleesExtra.normalnc_eq]
  delta S1EntryCalleesExtra.normalnc_native
  exact ⟨_, _, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem normal_nc_fields_ensures {R : Type} :
    S1NormalME.Ensures (fun _ => True) (monadLift (NormalNCMemAttr ()) : SailME R MemoryAttributes) NormalNCFields := by
  intro state _
  obtain ⟨attrs, other, call, fields, registers, memory, events⟩ := normal_nc_fields_total state
  refine ⟨attrs, other, ?_, ⟨registers, memory, events⟩, fields⟩
  simp [monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, Functor.map, EStateM.map, call]

#print axioms icache_el20_eq
#print axioms dcache_el20_eq
#print axioms check_output_cache_sound
#print axioms normal_nc_fields_total
#print axioms normal_nc_fields_ensures
end ArmCertWalk
