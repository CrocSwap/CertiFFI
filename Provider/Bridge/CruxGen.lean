import Bridge.CruxCore
import Bridge.CruxNonProj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.CruxGenLNSym.
namespace ArmBridge.CruxGen

/-- Register frame of a form action's result map `R`: everything the step prelude/epilogue and the
    invariants read is unchanged, except gpr/SP/Z and NZCV. mem, events and choice fields are unconstrained. -/
structure ActFrame (t u : NativeState) : Prop where
  bbool : u.regs.bank_Bool = t.regs.bank_Bool
  feat : u.regs.FeatureImpl = t.regs.FeatureImpl
  pse : ({ u.regs.PSTATE with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 } : ProcState) = ({ t.regs.PSTATE with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 } : ProcState)
  btn : u.regs.BTypeNext = t.regs.BTypeNext
  bt : u.regs.__BranchTaken = t.regs.__BranchTaken
  pc : u.regs._PC = t.regs._PC
  b64 : u.regs.bank_BitVec_64 = t.regs.bank_BitVec_64
  b32 : u.regs.bank_BitVec_32 = t.regs.bank_BitVec_32
  bint : u.regs.bank_Int = t.regs.bank_Int
  ss : u.regs.ShouldAdvanceSS = t.regs.ShouldAdvanceSS
  it : u.regs.ShouldAdvanceIT = t.regs.ShouldAdvanceIT
  enc : u.regs.__ThisInstrEnc = t.regs.__ThisInstrEnc
  btt : u.regs.Branchtypetaken = t.regs.Branchtypetaken
  emu : u.regs.__emulator_termination_opcode = t.regs.__emulator_termination_opcode
  b128 : u.regs.bank_BitVec_128 = t.regs.bank_BitVec_128

theorem ps_of_erased (u t : ProcState)
    (h : ({ u with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 } : ProcState) = { t with N := 0#1, Z := 0#1, C := 0#1, V := 0#1 }) :
    u = { t with N := u.N, Z := u.Z, C := u.C, V := u.V } := by
  cases u; cases t
  simp only [ProcState.mk.injEq] at h ⊢
  simp_all

/-- Inputs a form action's observable result may depend on; all are preserved by the step prelude. -/
structure CongIn (t1 t2 : NativeState) : Prop where
  mem : t1.mem = t2.mem
  gpr : t1.regs.gpr = t2.regs.gpr
  sp : t1.regs.SP_EL0 = t2.regs.SP_EL0
  z : t1.regs._Z = t2.regs._Z
  ps : t1.regs.PSTATE = t2.regs.PSTATE
  sys : SysEq2 t2.regs t1.regs
  spx1 : t1.regs.SP_EL1 = t2.regs.SP_EL1
  spx2 : t1.regs.SP_EL2 = t2.regs.SP_EL2
  spx3 : t1.regs.SP_EL3 = t2.regs.SP_EL3
  el0 : t1.regs.PSTATE.EL = 0#2

/-- The action results agree on everything the projection reads that the action may write. -/
structure CongOut (u1 u2 : NativeState) : Prop where
  mem : u1.mem = u2.mem
  gpr : u1.regs.gpr = u2.regs.gpr
  sp : u1.regs.SP_EL0 = u2.regs.SP_EL0
  z : u1.regs._Z = u2.regs._Z
  n : u1.regs.PSTATE.N = u2.regs.PSTATE.N
  zf : u1.regs.PSTATE.Z = u2.regs.PSTATE.Z
  c : u1.regs.PSTATE.C = u2.regs.PSTATE.C
  v : u1.regs.PSTATE.V = u2.regs.PSTATE.V

/-- System state BranchPinsV2 reads that SysEq2/StepPins do not carry (eval 56fd, crypto 6b3d): debug-resource
    counts and MDCR_EL3 (its NSPB/NSPBE fields). Kept separate from memory's verbatim SysEq2. -/
structure BrSysEq (r r' : Regs) : Prop where
  nbp : r'.bank_Int .NUM_BREAKPOINTS = r.bank_Int .NUM_BREAKPOINTS
  nwp : r'.bank_Int .NUM_WATCHPOINTS = r.bank_Int .NUM_WATCHPOINTS
  nctx : r'.bank_Int .__num_ctx_breakpoints = r.bank_Int .__num_ctx_breakpoints
  mdcr3 : r'.bank_BitVec_64 .MDCR_EL3 = r.bank_BitVec_64 .MDCR_EL3

/-- Events/memory clause packaging (argument order fixes the pre-action state `T` and pre-fetch state `T0`
    by unification before their facts are checked). -/
theorem ev_intro_gen (s : NativeState) (w : BitVec 32) (fL : NativeState → Array Event)
    (fS : NativeState → oracleChoiceSource.α) (fO : NativeState → Std.ExtHashMap Nat Nat) (fC : NativeState → Nat)
    (fSO : NativeState → Array String)
    (hFetch : ∀ t : NativeState, t.regs = preFetchRegs s.regs → t.mem = s.mem → t.events = s.events →
      (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t =
        .ok (.__A64, w) { t with regs := clrGP (fetchRegs t.regs), events := t.events ++ fL t, choiceState := fS t,
                                  choiceOcc := fO t, cycleCount := fC t, sailOutput := fSO t })
    (R : NativeState → NativeState) (Fn : NativeState) (Ev : Array Event) (Mm : Std.ExtHashMap Nat (BitVec 8)) (T : NativeState)
    (hE : Ev = (R T).events) (hM : Mm = (R T).mem) (hO : CongOut Fn (R T)) (T0 : NativeState) (hT : T.events = s.events ++ fL T0)
    (hTm : T.mem = s.mem) (hTc : CongIn s T) (h1 : T0.regs = preFetchRegs s.regs) (h2 : T0.mem = s.mem) (h3 : T0.events = s.events) :
    ∃ t0 t' T' : NativeState, t0.regs = preFetchRegs s.regs ∧ t0.mem = s.mem ∧ t0.events = s.events ∧
      (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32)) t0 = .ok (.__A64, w) t' ∧
      T'.events = t'.events ∧ T'.mem = s.mem ∧ Ev = (R T').events ∧ Mm = (R T').mem ∧ CongIn s T' ∧ CongOut Fn (R T') :=
  ⟨T0, _, T, h1, h2, h3, hFetch T0 h1 h2 h3, by rw [hT, h3], hTm, hE, hM, hTc, hO⟩

end ArmBridge.CruxGen

