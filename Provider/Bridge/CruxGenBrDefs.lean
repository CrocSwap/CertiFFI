import Bridge.CruxGen
import Bridge.CruxNonProj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenBr
open ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore

/-- Register frame of a BRANCH action's result map: as `CruxGen.ActFrame` without `_PC`, `__BranchTaken`
    and `Branchtypetaken` (constrained by `hBR` / `hBTT` instead). -/
structure ActFrameBr (t u : NativeState) : Prop where
  bbool : ∀ k, k ≠ Bank_Bool.SPESamplePreviousBranchAddressValid → u.regs.bank_Bool k = t.regs.bank_Bool k
  feat : u.regs.FeatureImpl = t.regs.FeatureImpl
  pse : ({ u.regs.PSTATE with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 } : ProcState) = ({ t.regs.PSTATE with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 } : ProcState)
  btn : u.regs.BTypeNext = t.regs.BTypeNext
  b64 : u.regs.bank_BitVec_64 = t.regs.bank_BitVec_64
  b32 : u.regs.bank_BitVec_32 = t.regs.bank_BitVec_32
  bint : u.regs.bank_Int = t.regs.bank_Int
  ss : u.regs.ShouldAdvanceSS = t.regs.ShouldAdvanceSS
  it : u.regs.ShouldAdvanceIT = t.regs.ShouldAdvanceIT
  enc : u.regs.__ThisInstrEnc = t.regs.__ThisInstrEnc
  emu : u.regs.__emulator_termination_opcode = t.regs.__emulator_termination_opcode
  b128 : u.regs.bank_BitVec_128 = t.regs.bank_BitVec_128

/-- `CruxGen.CongIn` plus PC and `__BranchTaken` (branch targets are PC-relative). -/
structure CongInBr (t1 t2 : NativeState) : Prop where
  base : ArmBridge.CruxGen.CongIn t1 t2
  pc : t1.regs._PC = t2.regs._PC
  bt : t1.regs.__BranchTaken = t2.regs.__BranchTaken

/-- The states `hA` is used at: prelude states (CongIn with `s`), PC unchanged and `__BranchTaken` cleared. -/
structure PreBr (s t : NativeState) : Prop where
  base : ArmBridge.CruxGen.CongIn s t
  pc : t.regs._PC = s.regs._PC
  bt : t.regs.__BranchTaken = false
  btt : t.regs.Branchtypetaken ≠ BranchType.BranchType_RESET
  btn : t.regs.BTypeNext = 0#2
  bint : ∀ k, k ≠ Bank_Int.SEE → k ≠ Bank_Int.__clock_divider → k ≠ Bank_Int.__last_cycle_count →
    t.regs.bank_Int k = s.regs.bank_Int k
  st : _get_EDSCR_Type_STATUS (t.regs.bank_BitVec_32 ._EDSCR) = _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR)
  edesr : t.regs.bank_BitVec_32 .EDESR = s.regs.bank_BitVec_32 .EDESR
  b64 : ∀ k, k ≠ Bank_BitVec_64.PMCCNTR_EL0 → k ≠ Bank_BitVec_64.PMICNTR_EL0 → k ≠ Bank_BitVec_64.PMOVSSET_EL0 →
    k ≠ Bank_BitVec_64.PMOVSCLR_EL0 → k ≠ Bank_BitVec_64.BRBTS_EL1 → k ≠ Bank_BitVec_64.MDCCSR_EL0 →
    t.regs.bank_BitVec_64 k = s.regs.bank_BitVec_64 k

/-- `CruxGen.CongOut` plus `__BranchTaken` and `_PC` of the results. -/
structure CongOutBr (u1 u2 : NativeState) : Prop where
  base : ArmBridge.CruxGen.CongOut u1 u2
  bt : u1.regs.__BranchTaken = u2.regs.__BranchTaken
  pc : u1.regs._PC = u2.regs._PC

/-- The model epilogue's conditional PC advance as ONE state update with a conditional PC. -/
theorem bif_pc (b : Bool) (A B : SailM Unit) (u : NativeState) (pc' : BitVec 64)
    (hA : A u = .ok () { u with regs := { u.regs with _PC := pc' } }) (hB : B u = .ok () u) :
    ((bif !b then A else B) : SailM Unit) u = .ok () { u with regs := { u.regs with _PC := if b then u.regs._PC else pc' } } := by
  cases b
  · simpa using hA
  · simpa using hB

theorem pc_cong (u1 u2 : NativeState) (h : CongOutBr u1 u2) :
    (if u1.regs.__BranchTaken then u1.regs._PC else u1.regs._PC + 4#64) =
      (if u2.regs.__BranchTaken then u2.regs._PC else
        (Sail.BitVec.extractLsb (BitVec.addInt u2.regs._PC (fdiv_int 32 8)) 63 0 : BitVec 64)) := by
  rw [h.bt, h.pc, pc4]

theorem sysEq2_comb {r1 r2 r : Regs} (h1 : SysEq2 r1 r) (h2 : SysEq2 r2 r) : SysEq2 r2 r1 :=
  ⟨h1.feat.symm.trans h2.feat, h1.el.symm.trans h2.el, h1.nrw.symm.trans h2.nrw, h1.sctlr.symm.trans h2.sctlr, h1.tcr.symm.trans h2.tcr, h1.tcr2.symm.trans h2.tcr2, h1.hcr.symm.trans h2.hcr, h1.scr.symm.trans h2.scr, h1.mair.symm.trans h2.mair, h1.mdscr.symm.trans h2.mdscr, h1.httbr.symm.trans h2.httbr, h1.ttbr0.symm.trans h2.ttbr0, h1.ttbr1.symm.trans h2.ttbr1, h1.hde.symm.trans h2.hde, h1.tlb.symm.trans h2.tlb, h1.spe.symm.trans h2.spe, h1.pa.symm.trans h2.pa⟩

theorem congInBr_of_pre {s t1 t2 : NativeState} (h1 : PreBr s t1) (h2 : PreBr s t2) : CongInBr t1 t2 :=
  ⟨⟨h1.base.mem.symm.trans h2.base.mem, h1.base.gpr.symm.trans h2.base.gpr, h1.base.sp.symm.trans h2.base.sp,
    h1.base.z.symm.trans h2.base.z, h1.base.ps.symm.trans h2.base.ps, sysEq2_comb h1.base.sys h2.base.sys,
    h1.base.spx1.symm.trans h2.base.spx1, h1.base.spx2.symm.trans h2.base.spx2, h1.base.spx3.symm.trans h2.base.spx3,
    h1.base.ps ▸ h1.base.el0⟩, h1.pc.trans h2.pc.symm, h1.bt.trans h2.bt.symm⟩

/-- Congruence makes the branch outcome the same on every prelude state. -/
theorem bt_const (s : NativeState) (R : NativeState → NativeState)
    (hCong : ∀ t1 t2, CongInBr t1 t2 → CongOutBr (R t1) (R t2)) :
    ∃ b0 : Bool, ∀ t, PreBr s t → (R t).regs.__BranchTaken = b0 := by
  by_cases h : ∃ t, PreBr s t ∧ (R t).regs.__BranchTaken = true
  · obtain ⟨w, hw, hb⟩ := h
    exact ⟨true, fun t ht => ((hCong t w (congInBr_of_pre ht hw)).bt).trans hb⟩
  · refine ⟨false, fun t ht => ?_⟩
    cases hb : (R t).regs.__BranchTaken
    · rfl
    · exact absurd ⟨t, ht, hb⟩ h

theorem pc4' (a b : BitVec 64) (h : a = b) :
    a + 4#64 = (Sail.BitVec.extractLsb (BitVec.addInt b (fdiv_int 32 8)) 63 0 : BitVec 64) := by rw [h, pc4]

theorem ev_intro_br (s : NativeState) (w : BitVec 32) (fL : NativeState → Array Event)
    (fS : NativeState → oracleChoiceSource.α) (fO : NativeState → Std.ExtHashMap Nat Nat) (fC : NativeState → Nat)
    (fSO : NativeState → Array String)
    (hFetch : ∀ t : NativeState, t.regs = preFetchRegs s.regs → t.mem = s.mem → t.events = s.events →
      (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t =
        .ok (.__A64, w) { t with regs := clrGP (fetchRegs t.regs), events := t.events ++ fL t, choiceState := fS t,
                                  choiceOcc := fO t, cycleCount := fC t, sailOutput := fSO t })
    (R : NativeState → NativeState)
    (hBR : ∀ t, ((R t).regs.__BranchTaken = t.regs.__BranchTaken ∧ (R t).regs._PC = t.regs._PC) ∨ (R t).regs.__BranchTaken = true)
    (Fn : NativeState) (Ev : Array Event) (Mm : Std.ExtHashMap Nat (BitVec 8)) (Pc : BitVec 64) (T : NativeState)
    (hE : Ev = (R T).events) (hM : Mm = (R T).mem) (hO : ArmBridge.CruxGen.CongOut Fn (R T))
    (hP : Pc = if (R T).regs.__BranchTaken then (R T).regs._PC else
      (Sail.BitVec.extractLsb (BitVec.addInt (R T).regs._PC (fdiv_int 32 8)) 63 0 : BitVec 64))
    (T0 : NativeState) (hT : T.events = s.events ++ fL T0) (hTm : T.mem = s.mem) (hTpc : T.regs._PC = s.regs._PC)
    (hTbt : T.regs.__BranchTaken = false) (hTp : PreBr s T)
    (h1 : T0.regs = preFetchRegs s.regs) (h2 : T0.mem = s.mem) (h3 : T0.events = s.events) :
    ∃ t0 t' T' : NativeState, t0.regs = preFetchRegs s.regs ∧ t0.mem = s.mem ∧ t0.events = s.events ∧
      (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t0 = .ok (.__A64, w) t' ∧
      T'.events = t'.events ∧ T'.mem = s.mem ∧ Ev = (R T').events ∧ Mm = (R T').mem ∧
      (Pc = if (R T').regs.__BranchTaken then (R T').regs._PC else s.regs._PC + 4#64) ∧ PreBr s T' ∧ ArmBridge.CruxGen.CongOut Fn (R T') := by
  refine ⟨T0, _, T, h1, h2, h3, hFetch T0 h1 h2 h3, by rw [hT, h3], hTm, hE, hM, ?_, hTp, hO⟩
  rw [hP]
  rcases hBR T with ⟨hb, hp⟩ | hb
  · rw [hb, hTbt, hp, hTpc, pc4]
  · rw [hb]
    rfl

end ArmBridge.CruxGenBr
