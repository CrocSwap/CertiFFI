import Walk.InitTLBFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace InitTLBSetup
abbrev State := InitTLBFrame.State

theorem of_model_run (s t : State) (hr : sail_model_init () s = .ok () t) :
    t.regs.bank_Bool .__tlb_enabled = false := by
  have h := InitTLBFrame.model_tlb s
  rw [hr] at h
  exact Option.some.inj h

theorem of_initial_run (oracle : Oracle) (t : State)
    (hr : ArmFull.initialState oracle = .ok () t) :
    t.regs.bank_Bool .__tlb_enabled = false := by
  have h := InitTLBFrame.initial_tlb oracle
  rw [hr] at h
  exact Option.some.inj h

theorem regs_frame (s t : State) (hr : t.regs = s.regs)
    (h : s.regs.bank_Bool .__tlb_enabled = false) :
    t.regs.bank_Bool .__tlb_enabled = false := by rw [hr]; exact h

theorem memory_frame (s : State) (m : Std.ExtHashMap Nat (BitVec 8)) :
    ({s with mem := m} : State).regs.bank_Bool .__tlb_enabled =
      s.regs.bank_Bool .__tlb_enabled := rfl

theorem write64 (key : Bank_BitVec_64) (v : BitVec 64) :
    InitTLBProperties.Keeps (writeReg (Regs.ref_BitVec_64 key) v) := by
  intro s
  exact ⟨(), _, rfl, rfl⟩

theorem write32 (key : Bank_BitVec_32) (v : BitVec 32) :
    InitTLBProperties.Keeps (writeReg (Regs.ref_BitVec_32 key) v) := by
  intro s
  exact ⟨(), _, rfl, rfl⟩

theorem write_int (key : Bank_Int) (v : Int) :
    InitTLBProperties.Keeps (writeReg (Regs.ref_Int key) v) := by
  intro s
  exact ⟨(), _, rfl, rfl⟩

theorem write_features (v : Vector Bool 259) :
    InitTLBProperties.Keeps (writeReg ArmFull.Register.FeatureImpl v) := by
  intro s
  exact ⟨(), _, rfl, rfl⟩

theorem write_pstate (v : ProcState) :
    InitTLBProperties.Keeps (writeReg ArmFull.Register.PSTATE v) := by
  intro s
  exact ⟨(), _, rfl, rfl⟩

theorem write_guard (v : Bool) :
    InitTLBProperties.Keeps (writeReg ArmFull.Register.InGuardedPage v) := by
  intro s
  exact ⟨(), _, rfl, rfl⟩

#print axioms of_initial_run
#print axioms write64
#print axioms write_features
end InitTLBSetup
