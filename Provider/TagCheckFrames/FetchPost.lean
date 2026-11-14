-- Additive stronger variant of canonical `ArmCert.Eval.M1a.Fetch2.fetch_frame` (proof pinned
-- from it). Differences: the read may CHANGE memory (actual walk AF/dirty stores), the word is
-- existential (actual post-walk content), and no event-append shape is imposed on the read.
import TagCheckFrames.ReadNoTag
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option Elab.async false
set_option maxRecDepth 10000
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedVariables false
namespace ArmCertWalk
open S1Normality ArmCert.Eval.M1a.Fetch2

/-- Actual `__FetchInstr` wrapper (draws 7632..7636, CreateAccDescIFetch,
SetBTypeCompatible false, CheckSoftwareStep, nRW branch, CheckPCAlignment,
PC_read, MemSingle_read, CheckIllegalState) around an arbitrary actual read.
`MB` is internal composition only, discharged from actual current data. -/
theorem fetch_frame_post_choice (s : ArmCert.Eval.M1a.Fetch2.State) (h : StepFacts s.regs)
    (hpc : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) (hil : s.regs.PSTATE.IL = 0#1)
    (Post : AccessDescriptor → ArmCert.Eval.M1a.Fetch2.State → BitVec 32 →
      ArmCert.Eval.M1a.Fetch2.State → Prop)
    (HA : ∀ t : ArmCert.Eval.M1a.Fetch2.State, t.regs = s.regs → t.mem = s.mem → t.events = s.events →
      ∃ acc u, CreateAccDescIFetch () t = .ok acc u ∧ Frame t u)
    (MB : ∀ acc, (∃ t0 u0 : ArmCert.Eval.M1a.Fetch2.State, t0.regs = s.regs ∧
        CreateAccDescIFetch () t0 = .ok acc u0) →
      ∀ t : ArmCert.Eval.M1a.Fetch2.State, t.regs = fetchRegs s.regs → t.mem = s.mem →
        t.events = s.events →
      ∃ word u, AArch64_MemSingle_read s.regs._PC 4 acc true t = .ok word u ∧
        u.regs.PSTATE.IL = t.regs.PSTATE.IL ∧ TagCheckFrames.Delta t u ∧ Post acc t word u) :
    ∃ acc t word u final, __FetchInstr s.regs._PC s = .ok (__InstrEnc.__A64, word) final ∧
      (∃ t0 u0 : ArmCert.Eval.M1a.Fetch2.State, t0.regs = s.regs ∧
        CreateAccDescIFetch () t0 = .ok acc u0) ∧
      t.regs = fetchRegs s.regs ∧ t.mem = s.mem ∧ t.events = s.events ∧ Post acc t word u ∧
      final.regs = u.regs ∧ final.mem = u.mem ∧ final.events = u.events ∧ TagCheckFrames.Delta s final := by
  rcases bits_normal 16 (.site 7632) s with ⟨x1, s1, h1, f1⟩
  rcases bits_normal 16 (.site 7633) s1 with ⟨x2, s2, h2, f2⟩
  rcases ArmCert.Eval.M1a.Fetch.bool_normal (.site 7634) s2 with ⟨x3, s3, h3, f3⟩
  rcases enc_normal (.site 7635) s3 with ⟨x4, s4, h4, f4⟩
  rcases bits_normal 32 (.site 7636) s4 with ⟨x5, s5, h5, f5⟩
  have f05 := ArmCert.Eval.JointSAT.Regime.frame_trans
    (ArmCert.Eval.JointSAT.Regime.frame_trans (ArmCert.Eval.JointSAT.Regime.frame_trans
      (ArmCert.Eval.JointSAT.Regime.frame_trans f1 f2) f3) f4) f5
  rcases HA s5 f05.1 f05.2.1 f05.2.2 with ⟨acc, s6, h6, f6⟩
  have hacc : ∃ t0 u0 : ArmCert.Eval.M1a.Fetch2.State, t0.regs = s.regs ∧
      CreateAccDescIFetch () t0 = .ok acc u0 :=
    ⟨s5, s6, f05.1, h6⟩
  have f06 := ArmCert.Eval.JointSAT.Regime.frame_trans f05 f6
  have h7r : StepFacts (Register.BTypeCompatible.set false s6.regs) := by
    rw [f06.1]
    obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, nrw, rme, ns, ss⟩ := h
    exact ⟨a0, a1, a2, a3, b0, b1, b2, b3, nrw, rme, ns, ss⟩
  rcases css_step { s6 with regs := Register.BTypeCompatible.set false s6.regs } h7r with
    ⟨s8, h8, r8, m8, e8⟩
  have r8' : s8.regs = fetchRegs s.regs := by
    rw [r8]
    show _ = Register.__InstructionStep.set false (Register.BTypeCompatible.set false s.regs)
    rw [← f06.1]
  have hpc8 : Sail.BitVec.extractLsb s8.regs._PC 1 0 = 0#2 := by rw [r8']; exact hpc
  have hnrw8 : s8.regs.PSTATE.nRW = 0#1 := by rw [r8']; exact h.nrw
  have hpcv : s8.regs._PC = s.regs._PC := by rw [r8']; rfl
  rcases MB acc hacc s8 r8' (m8.trans f06.2.1) (e8.trans f06.2.2) with ⟨word, u, h9, il9, d9, p9⟩
  have hil9 : u.regs.PSTATE.IL = 0#1 := by rw [il9, r8']; exact hil
  rcases ArmCert.Eval.M1a.Fetch.cis u hil9 with ⟨s10, h10, f10⟩
  have d1 := TagCheckFrames.bits_preserves 16 (.site 7632) s x1 s1 h1
  have d2 := TagCheckFrames.bits_preserves 16 (.site 7633) s1 x2 s2 h2
  have d3 := TagCheckFrames.bool_preserves (.site 7634) s2 x3 s3 h3
  have d4 := TagCheckFrames.enc_preserves (.site 7635) s3 x4 s4 h4
  have d5 := TagCheckFrames.bits_preserves 32 (.site 7636) s4 x5 s5 h5
  have d6 := TagCheckFrames.create_ifetch_preserves s5 acc s6 h6
  have d8 := TagCheckFrames.css_preserves { s6 with regs := Register.BTypeCompatible.set false s6.regs } () s8 h8
  have d10 := TagCheckFrames.cis_preserves u () s10 h10
  have d08 : TagCheckFrames.Delta s s8 :=
    NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans d1 d2) d3) d4) d5) d6) d8
  have dfinal := NativeMteTagCheck.choice_delta_trans (NativeMteTagCheck.choice_delta_trans d08 d9) d10
  refine ⟨acc, s8, word, u, s10, ?_, hacc, r8', m8.trans f06.2.1, e8.trans f06.2.2, p9,
    f10.1, f10.2.1, f10.2.2, dfinal⟩
  unfold __FetchInstr SetBTypeCompatible PC_read
  simp only [h1, h2, h3, h4, h5, h6, ArmCert.Eval.M1a.Fetch.pca s8 hpc8, h8, hnrw8, hpcv, h9, h10,
    PreSail.readReg_apply, PreSail.writeReg_apply, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure, readReg, writeReg, ↓reduceIte, beq_self_eq_true]
  have hnrw8' : ((Register.PSTATE.get s8.regs).nRW == 0#1) = true := by
    show (s8.regs.PSTATE.nRW == 0#1) = true
    rw [hnrw8]; rfl
  have hpcv' : Register._PC.get s8.regs = s.regs._PC := hpcv
  rw [if_pos hnrw8']
  simp only [EStateM.bind, ArmCert.Eval.M1a.Fetch.pca s8 hpc8, PreSail.readReg_apply, hpcv', h9, h10,
    EStateM.pure]

#print axioms fetch_frame_post_choice
end ArmCertWalk
