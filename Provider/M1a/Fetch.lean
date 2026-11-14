import M1a.FetchBase
import JointEL10.Regime20
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.Fetch2
/- __FetchInstr frame.
   Split agreed with armcert-memory: eval proves the wrapper (draws, CreateAccDescIFetch,
   SetBTypeCompatible, CheckSoftwareStep, CheckPCAlignment, PC_read, CheckIllegalState);
   memory supplies (M-b), the event-exact AArch64_MemSingle_read at PC, as hypothesis MB.
   CreateAccDescIFetch success is hypothesis HA; armcert-memory MemM1.AccIF.create proves it at
   EL0 (incl. the MPAM leg). v10 (defects d5148c84 R1): the fetched word is MB's read value.
 v11: the event list L is produced by MB per (acc, t) with a caller-chosen
   shape predicate P acc L (memory MBIF.MB_gen: translationStart ti ++ TTW reads ++
   translationEnd ad ++ ifetch memRead), and the conclusion exposes acc and L. -/
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

drive_spec ea_native, ea_eq : fun (el : BitVec 2) (s : State) => ELUsingAArch32 el s
drive_spec dtf_native, dtf_eq : fun (ss : SecurityState) (s : State) => DebugTargetFrom ss s
drive_spec dls_native, dls_eq : fun (s : State) => DoubleLockStatus () s
drive_spec hlt_native, hlt_eq : fun (s : State) => Halted () s
drive_spec sel2_native, sel2_eq : fun (s : State) => IsSecureEL2Enabled () s
drive_spec sder_native, sder_eq : fun (s : State) => SDER32_EL3_read () s

/-- GB10 AArch64-only feature facts (fv[0..2]=AA32EL0..2 false; fv[3]=AA32EL3 false; fv[4..7]=AA64 true). -/
structure A64Only (s : State) : Prop where
  a0 : s.regs.FeatureImpl[0] = false
  a1 : s.regs.FeatureImpl[1] = false
  a2 : s.regs.FeatureImpl[2] = false
  a3 : s.regs.FeatureImpl[3] = false
  b0 : s.regs.FeatureImpl[4] = true
  b1 : s.regs.FeatureImpl[5] = true
  b2 : s.regs.FeatureImpl[6] = true
  b3 : s.regs.FeatureImpl[7] = true
  nrw : s.regs.PSTATE.nRW = 0#1

theorem ex_ite1 {ε σ α : Type} (c : Prop) [Decidable c] (x y : EStateM.Result ε σ α) (v : α)
    (P : σ → Prop) (hx : c → ∃ t, x = .ok v t ∧ P t)
    (hy : ¬c → ∃ t, y = .ok v t ∧ P t) :
    ∃ t, (if c then x else y) = .ok v t ∧ P t := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h

theorem ea_ok (el : BitVec 2) (hel : el ≠ 0#2) (s : State) (h : A64Only s) :
    ∃ t, ELUsingAArch32 el s = .ok false t ∧ Frame s t := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, nrw⟩ := h
  rw [ea_eq]
  have : el = 1#2 ∨ el = 2#2 ∨ el = 3#2 := by bv_omega
  rcases this with rfl|rfl|rfl <;>
    (observe_simp [Frame, ea_native]) <;> simp [a0, a1, a2, a3, b0, b1, b2, b3, nrw] <;>
    (repeat (first
      | exact ⟨_, rfl, rfl, rfl, rfl⟩
      | (apply ex_ite1 <;> intro hc <;> simp only [hc, if_true, if_false, dite_true, dite_false,
            ite_true, ite_false, not_false_eq_true, not_true_eq_false, and_self, true_and, and_true,
            nrw])))

theorem dtf_normal (ss : SecurityState) : Normal (DebugTargetFrom ss) := by
  intro s; rw [dtf_eq]; observe_simp [Frame, dtf_native]
  all_goals (first | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ | exact ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩)


theorem dtf_ok (ss : SecurityState) (s : State) :
    ∃ v t, DebugTargetFrom ss s = .ok v t ∧ v ≠ 0#2 ∧ Frame s t := by
  rw [dtf_eq]; observe_simp [Frame, dtf_native]
  all_goals (first
    | exact ⟨_, _, ⟨rfl, rfl⟩, by (repeat' split) <;> decide, rfl, rfl, rfl⟩
    | exact ⟨_, _, rfl, rfl, by (repeat' split) <;> decide, rfl, rfl, rfl⟩)

theorem readReg_normal {α : Type} (r : RegisterRef Regs α) : Normal (readReg r : SailM α) := by
  intro s; exact ⟨_, _, PreSail.readReg_apply _ _, rfl, rfl, rfl⟩

theorem dls_normal : Normal (DoubleLockStatus ()) := by
  intro s; rw [dls_eq]; simp only [dls_native]
  refine ⟨_, _, rfl, ?_⟩; unfold Frame
  (repeat' split) <;> exact ⟨rfl, rfl, rfl⟩
theorem hlt_normal : Normal (Halted ()) := by
  intro s; rw [hlt_eq]; simp only [hlt_native]
  refine ⟨_, _, rfl, ?_⟩; unfold Frame
  (repeat' split) <;> exact ⟨rfl, rfl, rfl⟩
theorem sel2_normal : Normal (IsSecureEL2Enabled ()) := by
  intro s; rw [sel2_eq]; simp only [sel2_native]
  refine ⟨_, _, rfl, ?_⟩; unfold Frame
  (repeat' split) <;> exact ⟨rfl, rfl, rfl⟩
theorem sder_normal : Normal (SDER32_EL3_read ()) := by
  intro s; rw [sder_eq]; simp only [sder_native]
  refine ⟨_, _, rfl, ?_⟩; unfold Frame
  (repeat' split) <;> exact ⟨rfl, rfl, rfl⟩
theorem gdef_normal (el : BitVec 2) (ss : SecurityState) (m : BitVec 1) :
    Normal (AArch64_GenerateDebugExceptionsFrom el ss m) := by
  unfold AArch64_GenerateDebugExceptionsFrom
  repeat' (first
    | exact readReg_normal _
    | exact dls_normal | exact hlt_normal | exact sel2_normal | exact sder_normal
    | exact occ_normal _ | exact Fetch.bool_normal _ | exact pure_normal _
    | intro _
    | apply ite_normal
    | apply bind_normal
    | exact ⟨_, _, rfl, rfl, rfl, rfl⟩)

/-- Register facts the software-step check needs (AArch64-only, RME off, NS, no step). -/
structure StepFacts (r : Regs) : Prop where
  a0 : r.FeatureImpl[0] = false
  a1 : r.FeatureImpl[1] = false
  a2 : r.FeatureImpl[2] = false
  a3 : r.FeatureImpl[3] = false
  b0 : r.FeatureImpl[4] = true
  b1 : r.FeatureImpl[5] = true
  b2 : r.FeatureImpl[6] = true
  b3 : r.FeatureImpl[7] = true
  nrw : r.PSTATE.nRW = 0#1
  rme : r.FeatureImpl[232] = false
  ns : Sail.BitVec.extractLsb (r.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1
  ss : _get_MDSCR_EL1_Type_SS (r.bank_BitVec_64 .MDSCR_EL1) = 0#1

theorem StepFacts.a64 {s : State} (h : StepFacts s.regs) : A64Only s :=
  ⟨h.a0, h.a1, h.a2, h.a3, h.b0, h.b1, h.b2, h.b3, h.nrw⟩

theorem css_step (s : State) (h : StepFacts s.regs) :
    ∃ t, CheckSoftwareStep () s = .ok () t ∧
      t.regs = Register.__InstructionStep.set false s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases ArmCert.Eval.JointSAT.Regime.css s h.rme h.b0 h.ns with ⟨x1, s1, h1, f1⟩
  rcases dtf_ok x1 s1 with ⟨v, s2, h2, hv, f2⟩
  have f02 := ArmCert.Eval.JointSAT.Regime.frame_trans f1 f2
  have h2r : StepFacts s2.regs := f02.1 ▸ h
  rcases ea_ok v hv s2 h2r.a64 with ⟨s3, h3, f3⟩
  have f03 := ArmCert.Eval.JointSAT.Regime.frame_trans f02 f3
  have h3r : StepFacts s3.regs := f03.1 ▸ h
  rcases ArmCert.Eval.JointSAT.Regime.css s3 h3r.rme h3r.b0 h3r.ns with ⟨x2, s4, h4, f4⟩
  have f04 := ArmCert.Eval.JointSAT.Regime.frame_trans f03 f4
  rcases gdef_normal (Register.PSTATE.get s4.regs).EL x2 (Register.PSTATE.get s4.regs).D s4 with ⟨b, s5, h5, f5⟩
  have f05 := ArmCert.Eval.JointSAT.Regime.frame_trans f04 f5
  have hss : _get_MDSCR_EL1_Type_SS (Register.MDSCR_EL1.get s5.regs) = 0#1 := f05.1 ▸ h.ss
  unfold CheckSoftwareStep DebugTarget AArch64_GenerateDebugExceptions
  cases b with
  | false =>
    simp only [h1, h2, h3, h4, h5, PreSail.readReg_apply, PreSail.writeReg_apply, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, readReg, writeReg, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    exact ⟨_, rfl, by rw [f05.1], f05.2.1, f05.2.2⟩
  | true =>
    have e01 : ((0#1 : BitVec 1) == 1#1) = false := by decide
    simp only [h1, h2, h3, h4, h5, hss, e01, PreSail.readReg_apply, PreSail.writeReg_apply, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, readReg, writeReg, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    exact ⟨_, rfl, by rw [f05.1], f05.2.1, f05.2.2⟩

drive_spec enc_native, enc_eq : fun (l : ChoiceLabel) (s : State) => undefined___InstrEnc l () s

theorem enc_normal (l : ChoiceLabel) : Normal (undefined___InstrEnc l ()) := by
  intro s; rw [enc_eq]; observe_simp [Frame, enc_native]
  exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-- Registers after the fetch wrapper's own writes (BTypeCompatible := false, then the
    software-step check's __InstructionStep := false). -/
def fetchRegs (r : Regs) : Regs :=
  Register.__InstructionStep.set false (Register.BTypeCompatible.set false r)

theorem fetch_frame (s : State) (h : StepFacts s.regs)
    (hpc : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) (hil : s.regs.PSTATE.IL = 0#1)
    (word : BitVec 32) (P : AccessDescriptor → Array Event → Prop) (Q : Regs → Regs → Prop)
    (HA : ∀ t : State, t.regs = s.regs → t.mem = s.mem → t.events = s.events →
      ∃ acc u, CreateAccDescIFetch () t = .ok acc u ∧ Frame t u)
    (MB : ∀ acc, (∃ t0 u0 : State, t0.regs = s.regs ∧ CreateAccDescIFetch () t0 = .ok acc u0) →
      ∀ t : State, t.regs = fetchRegs s.regs → t.mem = s.mem → t.events = s.events →
      ∃ u L, AArch64_MemSingle_read s.regs._PC 4 acc true t = .ok word u ∧
        u.events = t.events ++ L ∧ P acc L ∧ Q t.regs u.regs ∧ u.regs.PSTATE.IL = t.regs.PSTATE.IL ∧
        u.mem = t.mem) :
    ∃ t acc L, __FetchInstr s.regs._PC s = .ok (__InstrEnc.__A64, word) t ∧
      (∃ t0 u0 : State, t0.regs = s.regs ∧ CreateAccDescIFetch () t0 = .ok acc u0) ∧
      Q (fetchRegs s.regs) t.regs ∧ t.mem = s.mem ∧ t.events = s.events ++ L ∧ P acc L := by
  rcases bits_normal 16 (.site 7632) s with ⟨x1, s1, h1, f1⟩
  rcases bits_normal 16 (.site 7633) s1 with ⟨x2, s2, h2, f2⟩
  rcases Fetch.bool_normal (.site 7634) s2 with ⟨x3, s3, h3, f3⟩
  rcases enc_normal (.site 7635) s3 with ⟨x4, s4, h4, f4⟩
  rcases bits_normal 32 (.site 7636) s4 with ⟨x5, s5, h5, f5⟩
  have f05 := ArmCert.Eval.JointSAT.Regime.frame_trans
    (ArmCert.Eval.JointSAT.Regime.frame_trans (ArmCert.Eval.JointSAT.Regime.frame_trans
      (ArmCert.Eval.JointSAT.Regime.frame_trans f1 f2) f3) f4) f5
  rcases HA s5 f05.1 f05.2.1 f05.2.2 with ⟨acc, s6, h6, f6⟩
  have hacc : ∃ t0 u0 : State, t0.regs = s.regs ∧ CreateAccDescIFetch () t0 = .ok acc u0 :=
    ⟨s5, s6, f05.1, h6⟩
  have f06 := ArmCert.Eval.JointSAT.Regime.frame_trans f05 f6
  have h7r : StepFacts (Register.BTypeCompatible.set false s6.regs) := by
    rw [f06.1]
    obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, nrw, rme, ns, ss⟩ := h
    exact ⟨a0, a1, a2, a3, b0, b1, b2, b3, nrw, rme, ns, ss⟩
  rcases css_step { s6 with regs := Register.BTypeCompatible.set false s6.regs } h7r with ⟨s8, h8, r8, m8, e8⟩
  have r8' : s8.regs = fetchRegs s.regs := by rw [r8]; show _ = Register.__InstructionStep.set false (Register.BTypeCompatible.set false s.regs); rw [← f06.1]
  have hpc8 : Sail.BitVec.extractLsb s8.regs._PC 1 0 = 0#2 := by rw [r8']; exact hpc
  have hnrw8 : s8.regs.PSTATE.nRW = 0#1 := by rw [r8']; exact h.nrw
  have hpcv : s8.regs._PC = s.regs._PC := by rw [r8']; rfl
  rcases MB acc hacc s8 r8' (m8.trans f06.2.1) (e8.trans f06.2.2) with ⟨u, L, h9, e9, p9, q9, il9, m9⟩
  have hil9 : u.regs.PSTATE.IL = 0#1 := by rw [il9, r8']; exact hil
  rcases Fetch.cis u hil9 with ⟨s10, h10, f10⟩
  refine ⟨s10, acc, L, ?_, hacc, ?_, ?_, ?_, p9⟩
  · unfold __FetchInstr SetBTypeCompatible PC_read
    simp only [h1, h2, h3, h4, h5, h6, Fetch.pca s8 hpc8, h8, hnrw8, hpcv, h9, h10,
      PreSail.readReg_apply, PreSail.writeReg_apply, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, readReg, writeReg, ↓reduceIte, beq_self_eq_true]
    have hnrw8' : ((Register.PSTATE.get s8.regs).nRW == 0#1) = true := by
      show (s8.regs.PSTATE.nRW == 0#1) = true
      rw [hnrw8]; rfl
    have hpcv' : Register._PC.get s8.regs = s.regs._PC := hpcv
    rw [if_pos hnrw8']
    simp only [EStateM.bind, Fetch.pca s8 hpc8, PreSail.readReg_apply, hpcv', h9, h10, EStateM.pure]
  · rw [f10.1, ← r8']; exact q9
  · rw [f10.2.1, m9, m8, f06.2.1]
  · rw [f10.2.2, e9, e8, f06.2.2]

#print axioms ea_ok
#print axioms dtf_ok
#print axioms gdef_normal
#print axioms css_step
#print axioms enc_normal
#print axioms fetch_frame
end ArmCert.Eval.M1a.Fetch2
