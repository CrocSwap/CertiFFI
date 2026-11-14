import Bridge.ModelStep
import Bridge.Awc
import Bridge.StepM
import BridgeV2.BoundaryV2
import Bridge.BKmin
import BKf.spePreP
import BKf.speCycleP
import Bridge.PremiseFree
import Bridge.CruxLemmas
import Bridge.TPImin
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxCore
open ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1

theorem ubool (ℓ : ChoiceLabel) (s : NativeState) :
    (undefined_bool_at ℓ () : SailM Bool) s = .ok (oracleChoiceSource.chooseAt .bool ℓ s.choiceState) s := rfl

theorem tc_apply {α : Type} (e : SailM α) (h : exception → SailM α) (s : NativeState) :
    (ArmFull.sailTryCatch e h : SailM α) s =
      match e s with
      | .ok a s' => .ok a s'
      | .error (.User u) s' => h u s'
      | .error ex s' => .error ex s' := by
  unfold ArmFull.sailTryCatch Sail.ConcurrencyInterfaceV1.PreSail.sailTryCatch
  show EStateM.tryCatch _ _ s = _
  unfold EStateM.tryCatch
  cases he : e s with
  | ok a s' => simp [he]
  | error ex s' => cases ex <;> simp [he, EStateM.throw, EStateM.dummyRestore, EStateM.dummySave] <;> rfl

theorem uenc (ℓ : ChoiceLabel) (s : NativeState) :
    ∃ e, (undefined___InstrEnc ℓ () : SailM __InstrEnc) s = .ok e s := by
  unfold undefined___InstrEnc internal_pick_at
  exact ⟨_, rfl⟩
theorem ubv (ℓ : ChoiceLabel) (n : Nat) (s : NativeState) :
    (undefined_bitvector_at ℓ n : SailM (BitVec n)) s = .ok (oracleChoiceSource.chooseAt (.bitvector n) ℓ s.choiceState) s := rfl

theorem bind_app {α β : Type} (x : SailM α) (f : α → SailM β) (s : NativeState) :
    (x >>= f) s = match x s with
      | .ok a s' => f a s'
      | .error e s' => .error e s' := by
  show EStateM.bind x f s = _
  unfold EStateM.bind
  cases x s <;> rfl

/-- Registers at the fetch call of the model step: SEE := -1 (step_model), EDSCR.PipeAdv/MDCCSR
update (EDSCR_write), ShouldAdvanceIT := false (AArch64), ShouldAdvanceSS := true. -/
def preFetchRegs (r : Regs) : Regs :=
  { r with
    bank_Int := (r.bank_Int.set .SEE (-1))
    ShouldAdvanceSS := true
    ShouldAdvanceIT := false
    bank_BitVec_32 := (r.bank_BitVec_32.set ._EDSCR
      (_update_EDSCR_Type_PipeAdv (Sail.BitVec.updateSubrange (r.bank_BitVec_32 ._EDSCR) 30 29
        (Sail.BitVec.slice (r.bank_BitVec_64 .MDCCSR_EL0) 29 2)) 1#1))
    bank_BitVec_64 := (r.bank_BitVec_64.set .MDCCSR_EL0
      (Sail.BitVec.updateSubrange (r.bank_BitVec_64 .MDCCSR_EL0) 30 29
        (Sail.BitVec.slice (_update_EDSCR_Type_PipeAdv (Sail.BitVec.updateSubrange (r.bank_BitVec_32 ._EDSCR) 30 29
          (Sail.BitVec.slice (r.bank_BitVec_64 .MDCCSR_EL0) 29 2)) 1#1) 29 2))) }

/-- eval m1a fetch_frame's register result (FetchBase.fetchRegs). -/
def fetchRegs (r : Regs) : Regs :=
  Register.__InstructionStep.set false (Register.BTypeCompatible.set false r)

/-- memory MemM1.IF.clrGP (the IFETCH translation clears InGuardedPage). -/
def clrGP (R : Regs) : Regs := { R with bank_Bool := RegMap.set R.bank_Bool .InGuardedPage false }

theorem pc_id (x : BitVec 64) : (Sail.BitVec.castWidth (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked 63) 0) : BitVec 64) = x := by
  rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have := x.isLt
  simp [Sail.Int.toNatChecked]
  omega

/-- E20 PMU frame: PMUEvent changes only PMU counter state. Stated as an
explicit field frame over everything the rest of the step reads or projects. -/
structure PMUFrame (r r' : Regs) : Prop where
  proj : ProjRegsEq r r'
  pstate : r'.PSTATE = r.PSTATE
  btn : r'.BTypeNext = r.BTypeNext
  bt : r'.__BranchTaken = r.__BranchTaken
  pc : r'._PC = r._PC
  feat : r'.FeatureImpl = r.FeatureImpl
  bbool : r'.bank_Bool = r.bank_Bool
  see : r'.bank_Int .SEE = r.bank_Int .SEE
  ss : r'.ShouldAdvanceSS = r.ShouldAdvanceSS
  it : r'.ShouldAdvanceIT = r.ShouldAdvanceIT
  emu : r'.__emulator_termination_opcode = r.__emulator_termination_opcode
  enc : r'.__ThisInstrEnc = r.__ThisInstrEnc
  hcr : r'.bank_BitVec_64 .HCR_EL2 = r.bank_BitVec_64 .HCR_EL2
  scr : r'.bank_BitVec_64 .SCR_EL3 = r.bank_BitVec_64 .SCR_EL3
  pmb : r'.bank_BitVec_64 .PMBLIMITR_EL1 = r.bank_BitVec_64 .PMBLIMITR_EL1
  mdscr : r'.bank_BitVec_64 .MDSCR_EL1 = r.bank_BitVec_64 .MDSCR_EL1
  edscr : r'.bank_BitVec_32 ._EDSCR = r.bank_BitVec_32 ._EDSCR
  thisInstr : r'.bank_BitVec_32 .__ThisInstr = r.bank_BitVec_32 .__ThisInstr
  pmbsr : r'.bank_BitVec_64 .PMBSR_EL1 = r.bank_BitVec_64 .PMBSR_EL1
  edecr : r'.bank_BitVec_32 .EDECR = r.bank_BitVec_32 .EDECR
  cti : r'.bank_BitVec_32 .CTIDEVCTL = r.bank_BitVec_32 .CTIDEVCTL
  edesr : r'.bank_BitVec_32 .EDESR = r.bank_BitVec_32 .EDESR
  btt : r'.Branchtypetaken = r.Branchtypetaken
  sctlr2 : r'.bank_BitVec_64 .SCTLR_EL2 = r.bank_BitVec_64 .SCTLR_EL2
  tcr2 : r'.bank_BitVec_64 .TCR2_EL2 = r.bank_BitVec_64 .TCR2_EL2
  mair : r'.bank_BitVec_64 .MAIR_EL2 = r.bank_BitVec_64 .MAIR_EL2
  httbr : r'.bank_BitVec_64 .HTTBR = r.bank_BitVec_64 .HTTBR
  b128 : r'.bank_BitVec_128 = r.bank_BitVec_128
  pa : r'.bank_Int .__supported_pa_size = r.bank_Int .__supported_pa_size
  sp1 : r'.SP_EL1 = r.SP_EL1
  sp2 : r'.SP_EL2 = r.SP_EL2
  sp3 : r'.SP_EL3 = r.SP_EL3

theorem defcond_a64 (t : NativeState) :
    (__DefaultCond __InstrEnc.__A64 : SailM (BitVec 4)) t =
      .ok 0xE#4 { t with choiceOcc := t.choiceOcc.insert 7631 (t.choiceOcc.getD 7631 0 + 1) } := by
  unfold __DefaultCond
  rfl

/-- Choice fields of a native result (state unchanged otherwise). -/
def resCS {α : Type} (t : NativeState) : EStateM.Result (Sail.Error exception) NativeState α → oracleChoiceSource.α
  | .ok _ u => u.choiceState
  | .error _ _ => t.choiceState
def resCO {α : Type} (t : NativeState) : EStateM.Result (Sail.Error exception) NativeState α → Std.ExtHashMap Nat Nat
  | .ok _ u => u.choiceOcc
  | .error _ _ => t.choiceOcc

/-- Frame from a projection root: if running `x` and then reading the non-choice fields gives the
initial fields back, `x` only moves the choice fields. -/
theorem unit_frame (x : SailM Unit) (t : NativeState) (X : NativeState)
    (h : ((do let _ ← x; let u ← get; pure (u.regs, u.mem, u.events, u.tags, u.cycleCount, u.sailOutput)) : SailM _) t =
      .ok (t.regs, t.mem, t.events, t.tags, t.cycleCount, t.sailOutput) X) :
    x t = .ok () { t with choiceState := resCS t (x t), choiceOcc := resCO t (x t) } := by
  revert h
  show EStateM.bind x _ t = _ → _
  unfold EStateM.bind
  cases hx : x t with
  | ok v u =>
    intro h
    simp only [resCS, resCO]
    have h' := h
    simp only [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind] at h'
    injection h' with h1 h2
    simp only [Prod.mk.injEq] at h1
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := h1
    cases u; cases v; simp_all
  | error e u => intro h; simp [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind] at h

#premise_min ArmBridge.CruxCore.spePreP_min from ArmBridge.BKf.spePreP_complete

theorem unit_frame' (x : SailM Unit) (t : NativeState) (X : NativeState) (v : Regs × Std.ExtHashMap Nat (BitVec 8) × Array Event × Unit × Nat × Array String)
    (h : ((do let _ ← x; let u ← get; pure (u.regs, u.mem, u.events, u.tags, u.cycleCount, u.sailOutput)) : SailM _) t =
      .ok v X) (hv : v = (t.regs, t.mem, t.events, t.tags, t.cycleCount, t.sailOutput)) :
    x t = .ok () { t with choiceState := resCS t (x t), choiceOcc := resCO t (x t) } := by
  subst hv; exact unit_frame x t X h

theorem bool_frame (x : SailM Bool) (t : NativeState) (X : NativeState)
    (h : ((do let b ← x; let u ← get; pure (b, u.regs, u.mem, u.events, u.tags, u.cycleCount, u.sailOutput)) : SailM _) t =
      .ok (false, t.regs, t.mem, t.events, t.tags, t.cycleCount, t.sailOutput) X) :
    x t = .ok false { t with choiceState := resCS t (x t), choiceOcc := resCO t (x t) } := by
  revert h
  show EStateM.bind x _ t = _ → _
  unfold EStateM.bind
  cases hx : x t with
  | ok v u =>
    intro h
    simp only [resCS, resCO]
    have h' := h
    simp only [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind] at h'
    injection h' with h1 h2
    simp only [Prod.mk.injEq] at h1
    obtain ⟨r0, r1, r2, r3, r4, r5, r6⟩ := h1
    subst r0
    cases u; simp_all
  | error e u => intro h; simp [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind] at h

theorem tpi_frame (req : InterruptReq) (t : NativeState)
    (h1 : t.regs.FeatureImpl[4]! = true) (h2 : t.regs.PSTATE.EL = 0#2) (h3 : t.regs.PSTATE.nRW = 0#1)
    (h4 : _get_HCR_EL2_Type_E2H (t.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (h5 : _get_HCR_EL2_Type_TGE (t.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (h6 : t.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (h7 : t.regs.PSTATE.A = 0#1) (h8 : t.regs.PSTATE.I = 0#1) (h9 : t.regs.PSTATE.F = 0#1) :
    (TakePendingInterrupts req : SailM Bool) t =
      .ok false { t with choiceState := resCS t ((TakePendingInterrupts req : SailM Bool) t),
                         choiceOcc := resCO t ((TakePendingInterrupts req : SailM Bool) t) } := by
  have hp := ArmBridge.TPImin.tpiP_min req t h1 h2 h3 h4 h5 h6 h7 h8 h9
  unfold ArmBridge.TPIF.tpiP_native at hp
  exact bool_frame _ t _ hp

theorem spePre_frame (real : Type) [Sail.SailReal real] (t : NativeState)
    (h1 : t.regs.FeatureImpl[4]! = true) (h2 : t.regs.FeatureImpl[232]! = false) (h3 : t.regs.PSTATE.EL = 0#2)
    (h4 : t.regs.PSTATE.nRW = 0#1) (h5 : _get_HCR_EL2_Type_E2H (t.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (h6 : _get_HCR_EL2_Type_TGE (t.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (h7 : _get_SCR_EL3_Type_NS (t.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (h8 : _get_PMBLIMITR_EL1_Type_E (t.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1) :
    (SPEPreExecution () : SailM Unit) t =
      .ok () { t with choiceState := resCS t ((SPEPreExecution () : SailM Unit) t),
                      choiceOcc := resCO t ((SPEPreExecution () : SailM Unit) t) } := by
  have hp := spePreP_min real t h1 h2 h3 h4 h5 h6 h7 h8
  unfold ArmBridge.BKf.spePreP_native at hp
  exact unit_frame _ t _ hp

theorem status_pipeadv (e : BitVec 32) (v : BitVec 2) :
    Sail.BitVec.extractLsb (_update_EDSCR_Type_PipeAdv (Sail.BitVec.updateSubrange e 30 29 v) 1#1) 5 0 =
      Sail.BitVec.extractLsb e 5 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : i < 6 := by simpa using hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;>
    simp [_update_EDSCR_Type_PipeAdv, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
      BitVec.getLsbD_extractLsb]

theorem hde_pipeadv (e : BitVec 32) (v : BitVec 2) :
    _get_EDSCR_Type_HDE (_update_EDSCR_Type_PipeAdv (Sail.BitVec.updateSubrange e 30 29 v) 1#1) =
      _get_EDSCR_Type_HDE e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : i = 0 := by simp at hi; omega
  subst this
  simp [_get_EDSCR_Type_HDE, _update_EDSCR_Type_PipeAdv, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb]

def resSt {α : Type} (t : NativeState) : EStateM.Result (Sail.Error exception) NativeState α → NativeState
  | .ok _ u => u
  | .error _ _ => t

#premise_min ArmBridge.CruxCore.speCycleP_min from ArmBridge.BKf.speCycleP_complete

theorem speCycle_frame (real : Type) [Sail.SailReal real] (t : NativeState)
    (h1 : t.regs.bank_Bool .SPESampleInFlight = false)
    (h2 : Sail.BitVec.extractLsb (t.regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1) :
    (SPECycle () : SailM Unit) t =
      .ok () { t with choiceState := resCS t ((SPECycle () : SailM Unit) t),
                      choiceOcc := resCO t ((SPECycle () : SailM Unit) t) } := by
  have hp := speCycleP_min real t h1
  unfold ArmBridge.BKf.speCycleP_native at hp
  refine unit_frame' _ t _ _ hp ?_
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; exact absurd h.1 (by decide))
    | (exfalso; simp_all)
    | (rename_i _ h _; rw [h2] at h; exact absurd h (by decide))

theorem ssadv_frame (t : NativeState) (h1 : t.regs.FeatureImpl[4]! = true) (h2 : t.regs.FeatureImpl[232]! = false)
    (h3 : t.regs.PSTATE.EL = 0#2) (h4 : _get_HCR_EL2_Type_TGE (t.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (h5 : _get_SCR_EL3_Type_NS (t.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (h6 : _get_MDSCR_EL1_Type_SS (t.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1) :
    (SSAdvance () : SailM Unit) t = .ok () { t with choiceOcc := resCO t ((SSAdvance () : SailM Unit) t) } := by
  rw [ArmBridge.BKmin.SSAdvance () t h1 h2 h3 h4 h5 h6]
  rfl

theorem pc4 (x : BitVec 64) :
    x + 4#64 = (Sail.BitVec.extractLsb (BitVec.addInt x (fdiv_int 32 8)) 63 0 : BitVec 64) := by
  have h : fdiv_int 32 8 = 4 := by decide
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.addInt, BitVec.toNat_add]

/-- E20 (a design decision) state set: PMU counter / overflow state (incl. the cycle-count
bookkeeping it uses and the overflow interrupt line, which falls under S8). -/
def eraseE20 (r : Regs) : Regs :=
  { r with
    PMUEventAccumulator := default
    PMULastThresholdValue := default
    bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32.set .PMEVCNTR_EL0 default
    bank_BitVec_64 := ((((r.bank_BitVec_64.set .PMCCNTR_EL0 0).set .PMICNTR_EL0 0).set .PMOVSSET_EL0 0).set
      .PMOVSCLR_EL0 0).set .BRBTS_EL1 0
    bank_Int := (r.bank_Int.set .__clock_divider 0).set .__last_cycle_count 0
    bank_Option_InterruptID := r.bank_Option_InterruptID.set .__GIC_Pending none }

/-- E22 state set: system counter and timer state (incl. the timer interrupt line, S8). -/
def eraseE22 (r : Regs) : Regs :=
  { r with
    PhysicalCount := default
    bank_BitVec_64 := (((((((r.bank_BitVec_64.set .CNTP_CTL_EL0 0).set .CNTV_CTL_EL0 0).set .CNTHP_CTL_EL2 0).set
      .CNTHV_CTL_EL2 0).set .CNTHPS_CTL_EL2 0).set .CNTHVS_CTL_EL2 0).set .CNTPS_CTL_EL1 0)
    bank_BitVec_32 := ((r.bank_BitVec_32.set .CNTP_CTL_S 0).set ._CNTHP_CTL 0).set ._CNTP_CTL_NS 0
    bank_BitVec_1 := r.bank_BitVec_1.set .EventRegister 0
    bank_Option_InterruptID := r.bank_Option_InterruptID.set .__GIC_Pending none }

/-- Premise E20: only PMU counter/overflow state changes. -/
def E20Frame (r r' : Regs) : Prop := eraseE20 r' = eraseE20 r
/-- Premise E22: only system-counter/timer state changes. -/
def E22Frame (r r' : Regs) : Prop := eraseE22 r' = eraseE22 r

theorem frame_pres_E20 {β : Type} (f : Regs → β) (hf : ∀ x, f (eraseE20 x) = f x) {r r' : Regs}
    (h : E20Frame r r') : f r' = f r := by
  rw [← hf r', ← hf r]; exact congrArg f h

theorem PMUFrame.of_E20 {r r' : Regs} (h : E20Frame r r') : PMUFrame r r' where
  proj := ⟨frame_pres_E20 (fun x => x.gpr) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x._Z) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x._PC) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.PSTATE.N) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.PSTATE.Z) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.PSTATE.C) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.PSTATE.V) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .TPIDR_EL0) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .TPIDRRO_EL0) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .DCZID_EL0) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .MIDR_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .ID_AA64ISAR1_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .ID_AA64ISAR2_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .ID_AA64MMFR1_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .TCR_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .TCR_EL2) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E20 (fun x => x.bank_BitVec_64 .HCR_EL2) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h⟩
  pstate := frame_pres_E20 (fun x => x.PSTATE) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  btn := frame_pres_E20 (fun x => x.BTypeNext) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  bt := frame_pres_E20 (fun x => x.__BranchTaken) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  pc := frame_pres_E20 (fun x => x._PC) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  feat := frame_pres_E20 (fun x => x.FeatureImpl) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  bbool := frame_pres_E20 (fun x => x.bank_Bool) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  see := frame_pres_E20 (fun x => x.bank_Int .SEE) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  ss := frame_pres_E20 (fun x => x.ShouldAdvanceSS) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  it := frame_pres_E20 (fun x => x.ShouldAdvanceIT) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  emu := frame_pres_E20 (fun x => x.__emulator_termination_opcode) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  enc := frame_pres_E20 (fun x => x.__ThisInstrEnc) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  hcr := frame_pres_E20 (fun x => x.bank_BitVec_64 .HCR_EL2) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  scr := frame_pres_E20 (fun x => x.bank_BitVec_64 .SCR_EL3) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  pmb := frame_pres_E20 (fun x => x.bank_BitVec_64 .PMBLIMITR_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  mdscr := frame_pres_E20 (fun x => x.bank_BitVec_64 .MDSCR_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  edscr := frame_pres_E20 (fun x => x.bank_BitVec_32 ._EDSCR) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  thisInstr := frame_pres_E20 (fun x => x.bank_BitVec_32 .__ThisInstr) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  pmbsr := frame_pres_E20 (fun x => x.bank_BitVec_64 .PMBSR_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  edecr := frame_pres_E20 (fun x => x.bank_BitVec_32 .EDECR) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  cti := frame_pres_E20 (fun x => x.bank_BitVec_32 .CTIDEVCTL) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  edesr := frame_pres_E20 (fun x => x.bank_BitVec_32 .EDESR) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  btt := frame_pres_E20 (fun x => x.Branchtypetaken) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  sctlr2 := frame_pres_E20 (fun x => x.bank_BitVec_64 .SCTLR_EL2) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  tcr2 := frame_pres_E20 (fun x => x.bank_BitVec_64 .TCR2_EL2) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  mair := frame_pres_E20 (fun x => x.bank_BitVec_64 .MAIR_EL2) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  httbr := frame_pres_E20 (fun x => x.bank_BitVec_64 .HTTBR) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  b128 := frame_pres_E20 (fun x => x.bank_BitVec_128) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  pa := frame_pres_E20 (fun x => x.bank_Int .__supported_pa_size) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  sp1 := frame_pres_E20 (fun x => x.SP_EL1) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  sp2 := frame_pres_E20 (fun x => x.SP_EL2) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  sp3 := frame_pres_E20 (fun x => x.SP_EL3) (fun x => by simp (disch := decide) only [eraseE20, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h

theorem frame_pres_E22 {β : Type} (f : Regs → β) (hf : ∀ x, f (eraseE22 x) = f x) {r r' : Regs}
    (h : E22Frame r r') : f r' = f r := by
  rw [← hf r', ← hf r]; exact congrArg f h

theorem PMUFrame.of_E22 {r r' : Regs} (h : E22Frame r r') : PMUFrame r r' where
  proj := ⟨frame_pres_E22 (fun x => x.gpr) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x._Z) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x._PC) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.PSTATE.N) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.PSTATE.Z) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.PSTATE.C) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.PSTATE.V) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .TPIDR_EL0) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .TPIDRRO_EL0) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .DCZID_EL0) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .MIDR_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .ID_AA64ISAR1_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .ID_AA64ISAR2_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .ID_AA64MMFR1_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .TCR_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .TCR_EL2) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h, frame_pres_E22 (fun x => x.bank_BitVec_64 .HCR_EL2) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h⟩
  pstate := frame_pres_E22 (fun x => x.PSTATE) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  btn := frame_pres_E22 (fun x => x.BTypeNext) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  bt := frame_pres_E22 (fun x => x.__BranchTaken) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  pc := frame_pres_E22 (fun x => x._PC) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  feat := frame_pres_E22 (fun x => x.FeatureImpl) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  bbool := frame_pres_E22 (fun x => x.bank_Bool) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  see := frame_pres_E22 (fun x => x.bank_Int .SEE) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  ss := frame_pres_E22 (fun x => x.ShouldAdvanceSS) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  it := frame_pres_E22 (fun x => x.ShouldAdvanceIT) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  emu := frame_pres_E22 (fun x => x.__emulator_termination_opcode) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  enc := frame_pres_E22 (fun x => x.__ThisInstrEnc) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  hcr := frame_pres_E22 (fun x => x.bank_BitVec_64 .HCR_EL2) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  scr := frame_pres_E22 (fun x => x.bank_BitVec_64 .SCR_EL3) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  pmb := frame_pres_E22 (fun x => x.bank_BitVec_64 .PMBLIMITR_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  mdscr := frame_pres_E22 (fun x => x.bank_BitVec_64 .MDSCR_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  edscr := frame_pres_E22 (fun x => x.bank_BitVec_32 ._EDSCR) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  thisInstr := frame_pres_E22 (fun x => x.bank_BitVec_32 .__ThisInstr) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  pmbsr := frame_pres_E22 (fun x => x.bank_BitVec_64 .PMBSR_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  edecr := frame_pres_E22 (fun x => x.bank_BitVec_32 .EDECR) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  cti := frame_pres_E22 (fun x => x.bank_BitVec_32 .CTIDEVCTL) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  edesr := frame_pres_E22 (fun x => x.bank_BitVec_32 .EDESR) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  btt := frame_pres_E22 (fun x => x.Branchtypetaken) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  sctlr2 := frame_pres_E22 (fun x => x.bank_BitVec_64 .SCTLR_EL2) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  tcr2 := frame_pres_E22 (fun x => x.bank_BitVec_64 .TCR2_EL2) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  mair := frame_pres_E22 (fun x => x.bank_BitVec_64 .MAIR_EL2) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  httbr := frame_pres_E22 (fun x => x.bank_BitVec_64 .HTTBR) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  b128 := frame_pres_E22 (fun x => x.bank_BitVec_128) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  pa := frame_pres_E22 (fun x => x.bank_Int .__supported_pa_size) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  sp1 := frame_pres_E22 (fun x => x.SP_EL1) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  sp2 := frame_pres_E22 (fun x => x.SP_EL2) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h
  sp3 := frame_pres_E22 (fun x => x.SP_EL3) (fun x => by simp (disch := decide) only [eraseE22, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]) h

/-- Register pins re-established by the step (the per-step premises other than S8's
__GIC_Pending = none, fetch and the program word). -/
structure StepPins (s : NativeState) : Prop where
  f4 : s.regs.FeatureImpl[4]! = true
  rme : s.regs.FeatureImpl[232]! = false
  spe : s.regs.bank_Bool .SPESampleInFlight = false
  el : s.regs.PSTATE.EL = 0#2
  nrw : s.regs.PSTATE.nRW = 0#1
  edecr : _get_EDECR_Type_RCE (s.regs.bank_BitVec_32 .EDECR) = 0#1
  cti : _get_CTIDEVCTL_Type_RCE (s.regs.bank_BitVec_32 .CTIDEVCTL) = 0#1
  st : _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6
  edesr : s.regs.bank_BitVec_32 .EDESR = 0#32
  btt : s.regs.Branchtypetaken ≠ BranchType.BranchType_RESET
  emu : s.regs.__emulator_termination_opcode = none
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  scrns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  pmbe : _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1
  mdss : _get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1
  pmbs : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1
  da : s.regs.PSTATE.A = 0#1
  di : s.regs.PSTATE.I = 0#1
  df : s.regs.PSTATE.F = 0#1
  il : s.regs.PSTATE.IL = 0#1
  pss : s.regs.PSTATE.SS = 0#1
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2

/-- Verbatim copy of memory `MemM1.StepInv2.SysEq2` (mem-v3-v5 ws/MemM1/StepInv2.lean:30); that package
    is not on this leanpath. Field order and statements identical, so `⟨h.1, …, h.17⟩` converts. -/
structure SysEq2 (r r' : Regs) : Prop where
  feat : r'.FeatureImpl = r.FeatureImpl
  el : r'.PSTATE.EL = r.PSTATE.EL
  nrw : r'.PSTATE.nRW = r.PSTATE.nRW
  sctlr : r'.bank_BitVec_64 .SCTLR_EL2 = r.bank_BitVec_64 .SCTLR_EL2
  tcr : r'.bank_BitVec_64 .TCR_EL2 = r.bank_BitVec_64 .TCR_EL2
  tcr2 : r'.bank_BitVec_64 .TCR2_EL2 = r.bank_BitVec_64 .TCR2_EL2
  hcr : r'.bank_BitVec_64 .HCR_EL2 = r.bank_BitVec_64 .HCR_EL2
  scr : r'.bank_BitVec_64 .SCR_EL3 = r.bank_BitVec_64 .SCR_EL3
  mair : r'.bank_BitVec_64 .MAIR_EL2 = r.bank_BitVec_64 .MAIR_EL2
  mdscr : r'.bank_BitVec_64 .MDSCR_EL1 = r.bank_BitVec_64 .MDSCR_EL1
  httbr : r'.bank_BitVec_64 .HTTBR = r.bank_BitVec_64 .HTTBR
  ttbr0 : r'.bank_BitVec_128 ._TTBR0_EL2 = r.bank_BitVec_128 ._TTBR0_EL2
  ttbr1 : r'.bank_BitVec_128 .TTBR1_EL2 = r.bank_BitVec_128 .TTBR1_EL2
  hde : _get_EDSCR_Type_HDE (r'.bank_BitVec_32 ._EDSCR) = _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR)
  tlb : r'.bank_Bool .__tlb_enabled = r.bank_Bool .__tlb_enabled
  spe : r'.bank_Bool .SPESampleInFlight = r.bank_Bool .SPESampleInFlight
  pa : r'.bank_Int .__supported_pa_size = r.bank_Int .__supported_pa_size

/-- The fetch premise in exactly the shape memory's `MemM1.MBV2.fetch_v2` delivers, at every pre-fetch
    state of this step (registers `preFetchRegs s.regs`, memory and events of `s`): the fetch returns
    (A64, w), registers become `clrGP (fetchRegs ·)` (memory's `QIF`), memory is unchanged and the only
    new events are some `L` (memory's `PIF … L`). Choice/cycle/output fields are unconstrained. -/
def FetchSpec (s : NativeState) (w : BitVec 32) : Prop :=
  ∀ t : NativeState, t.regs = preFetchRegs s.regs → t.mem = s.mem → t.events = s.events →
    ∃ t' : NativeState, ∃ L : Array Event, (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t = .ok (.__A64, w) t' ∧
      t'.regs = clrGP (fetchRegs t.regs) ∧ t'.mem = t.mem ∧ t'.events = t.events ++ L

theorem state_eta (t t' : NativeState) (R : Regs) (E : Array Event) (hr : t'.regs = R) (hm : t'.mem = t.mem)
    (he : t'.events = E) :
    t' = { t with regs := R, events := E, choiceState := t'.choiceState, choiceOcc := t'.choiceOcc,
                  cycleCount := t'.cycleCount, sailOutput := t'.sailOutput } := by
  cases t; cases t'; simp_all

open Classical in
/-- `FetchSpec` in the function form used inside the crux proofs (choice of the witnesses per state). -/
theorem fetch_fns (s : NativeState) (w : BitVec 32) (H : FetchSpec s w) :
    ∃ (fL : NativeState → Array Event) (fS : NativeState → oracleChoiceSource.α)
      (fO : NativeState → Std.ExtHashMap Nat Nat) (fC : NativeState → Nat) (fSO : NativeState → Array String),
      ∀ t : NativeState, t.regs = preFetchRegs s.regs → t.mem = s.mem → t.events = s.events →
        (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t =
          .ok (.__A64, w) { t with regs := clrGP (fetchRegs t.regs), events := t.events ++ fL t, choiceState := fS t,
                                    choiceOcc := fO t, cycleCount := fC t, sailOutput := fSO t } := by
  let g : NativeState → NativeState × Array Event := fun t =>
    if h : t.regs = preFetchRegs s.regs ∧ t.mem = s.mem ∧ t.events = s.events then
      (Classical.choose (H t h.1 h.2.1 h.2.2), Classical.choose (Classical.choose_spec (H t h.1 h.2.1 h.2.2)))
    else (t, #[])
  refine ⟨fun t => (g t).2, fun t => (g t).1.choiceState, fun t => (g t).1.choiceOcc, fun t => (g t).1.cycleCount,
    fun t => (g t).1.sailOutput, ?_⟩
  intro t h1 h2 h3
  have hp : t.regs = preFetchRegs s.regs ∧ t.mem = s.mem ∧ t.events = s.events := ⟨h1, h2, h3⟩
  obtain ⟨hf, hr, hm, he⟩ := Classical.choose_spec (Classical.choose_spec (H t hp.1 hp.2.1 hp.2.2))
  simp only [g, dif_pos hp]
  exact hf.trans (congrArg _ (state_eta t _ _ _ hr hm he))

/-- Packaging the events clause: argument order lets elaboration fix the pre-fetch state `T0` from the
    events equation before checking its register/memory/event facts. -/
theorem ev_intro (s : NativeState) (w : BitVec 32) (fL : NativeState → Array Event)
    (fS : NativeState → oracleChoiceSource.α) (fO : NativeState → Std.ExtHashMap Nat Nat) (fC : NativeState → Nat)
    (fSO : NativeState → Array String)
    (hFetch : ∀ t : NativeState, t.regs = preFetchRegs s.regs → t.mem = s.mem → t.events = s.events →
      (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t =
        .ok (.__A64, w) { t with regs := clrGP (fetchRegs t.regs), events := t.events ++ fL t, choiceState := fS t,
                                  choiceOcc := fO t, cycleCount := fC t, sailOutput := fSO t })
    (E : Array Event) (T0 : NativeState) (hE : E = s.events ++ fL T0)
    (h1 : T0.regs = preFetchRegs s.regs) (h2 : T0.mem = s.mem) (h3 : T0.events = s.events) :
    ∃ t0 t' : NativeState, t0.regs = preFetchRegs s.regs ∧ t0.mem = s.mem ∧ t0.events = s.events ∧
      (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t0 = .ok (.__A64, w) t' ∧ E = t'.events :=
  ⟨T0, _, h1, h2, h3, hFetch T0 h1 h2 h3, by rw [hE, h3]⟩

theorem ite_st {ε σ α : Type} (c : Prop) [Decidable c] (f g : EStateM ε σ α) (s : σ) :
    (if c then f else g) s = if c then f s else g s := by
  split <;> rfl

#print axioms fetch_fns
end ArmBridge.CruxCore
