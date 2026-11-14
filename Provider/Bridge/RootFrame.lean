import Bridge.CruxCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.RootFrame
open ArmBridge.CruxCore ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1

/-! Root-to-frame lemmas with the action and the root result abstract, so case analysis on `x t`
never has to type-check a (possibly huge) native term in its motive. -/

theorem frame_of_root {β : Type} (x : SailM Unit) (F : NativeState → β) (t u' : NativeState)
    (h : ((do let _ ← x; let u ← get; pure (F u)) : SailM β) t = .ok (F t) u') :
    x t = .ok () (resSt t (x t)) ∧ F (resSt t (x t)) = F t := by
  revert h
  show EStateM.bind _ _ t = _ → _
  unfold EStateM.bind
  cases hx : x t with
  | ok v u =>
    intro h
    simp only [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind] at h
    injection h with h1 h2
    exact ⟨rfl, by simp only [resSt]; exact h1⟩
  | error e u =>
    intro h
    simp only [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind] at h
    cases h

/-- The value of a root result, defaulting to `d` on error. -/
def resVal {β : Type} (d : β) : EStateM.Result (Sail.Error exception) NativeState β → β
  | .ok v _ => v
  | .error _ _ => d

theorem ok_of_root {β : Type} (x : SailM Unit) (F : NativeState → β) (t u' : NativeState) (v : β)
    (h : ((do let _ ← x; let u ← get; pure (F u)) : SailM β) t = .ok v u') :
    x t = .ok () (resSt t (x t)) := by
  revert h
  show EStateM.bind _ _ t = _ → _
  unfold EStateM.bind
  cases hx : x t with
  | ok w u => intro _; rfl
  | error e u =>
    intro h
    simp only [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind] at h
    cases h

theorem val_of_root {β : Type} (x : SailM Unit) (G : NativeState → β) (t : NativeState)
    (N : EStateM.Result (Sail.Error exception) NativeState β)
    (h : ((do let _ ← x; let u ← get; pure (G u)) : SailM β) t = N) :
    G (resSt t (x t)) = resVal (G t) N := by
  revert h
  show EStateM.bind _ _ t = N → _
  unfold EStateM.bind
  cases hx : x t with
  | ok v u =>
    intro h
    simp only [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind] at h
    subst h
    simp only [resSt, resVal]
  | error e u =>
    intro h
    simp only [get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind] at h
    subst h
    simp only [resSt, resVal]

/-- Sail's one-bit test `setWidth 1 (join1 [access y i])` as a non-dependent term, so simp can rewrite
    inside it (the type of `join1 [..]` depends on the list term). -/
theorem sw_join1 {n : Nat} (y : BitVec n) (i : Nat) :
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access y i]) = BitVec.access y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have : j = 0 := by omega
  subst this
  simp [Sail.BitVec.join1, Sail.BitVec.access]
  generalize y[i]! = b
  cases b <;> rfl

/-- Push `∃ u, _ = .ok v u` through a dependent if without rewriting the (possibly huge) branches. -/
theorem dite_ok {α σ ε : Type} {c : Prop} [Decidable c] {v : α} {t : c → EStateM.Result ε σ α}
    {e : ¬c → EStateM.Result ε σ α} (ht : ∀ h, ∃ u, t h = .ok v u) (he : ∀ h, ∃ u, e h = .ok v u) :
    ∃ u, (if h : c then t h else e h) = .ok v u := by
  by_cases h : c
  · rw [dif_pos h]; exact ht h
  · rw [dif_neg h]; exact he h

/-! Projections pushed through `if` (for state-level ifs in root natives, e.g. CSEL on condition flags). -/
theorem ite_sregs {c : Prop} [Decidable c] (a b : NativeState) : (if c then a else b).regs = if c then a.regs else b.regs := by split <;> rfl
theorem dite_sregs {c : Prop} [Decidable c] (a : c → NativeState) (b : ¬c → NativeState) :
    (if h : c then a h else b h).regs = if h : c then (a h).regs else (b h).regs := by split <;> rfl
theorem ite_smem {c : Prop} [Decidable c] (a b : NativeState) : (if c then a else b).mem = if c then a.mem else b.mem := by split <;> rfl
theorem dite_smem {c : Prop} [Decidable c] (a : c → NativeState) (b : ¬c → NativeState) :
    (if h : c then a h else b h).mem = if h : c then (a h).mem else (b h).mem := by split <;> rfl
theorem ite_sevents {c : Prop} [Decidable c] (a b : NativeState) : (if c then a else b).events = if c then a.events else b.events := by split <;> rfl
theorem dite_sevents {c : Prop} [Decidable c] (a : c → NativeState) (b : ¬c → NativeState) :
    (if h : c then a h else b h).events = if h : c then (a h).events else (b h).events := by split <;> rfl
theorem ite_rbank_Bool {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Bool = if c then a.bank_Bool else b.bank_Bool := by split <;> rfl
theorem dite_rbank_Bool {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Bool = if h : c then (a h).bank_Bool else (b h).bank_Bool := by split <;> rfl
theorem ite_rFeatureImpl {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).FeatureImpl = if c then a.FeatureImpl else b.FeatureImpl := by split <;> rfl
theorem dite_rFeatureImpl {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).FeatureImpl = if h : c then (a h).FeatureImpl else (b h).FeatureImpl := by split <;> rfl
theorem ite_rPSTATE {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).PSTATE = if c then a.PSTATE else b.PSTATE := by split <;> rfl
theorem dite_rPSTATE {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).PSTATE = if h : c then (a h).PSTATE else (b h).PSTATE := by split <;> rfl
theorem ite_rBTypeNext {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).BTypeNext = if c then a.BTypeNext else b.BTypeNext := by split <;> rfl
theorem dite_rBTypeNext {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).BTypeNext = if h : c then (a h).BTypeNext else (b h).BTypeNext := by split <;> rfl
theorem ite_rBranchTaken {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).__BranchTaken = if c then a.__BranchTaken else b.__BranchTaken := by split <;> rfl
theorem dite_rBranchTaken {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).__BranchTaken = if h : c then (a h).__BranchTaken else (b h).__BranchTaken := by split <;> rfl
theorem ite_rPC {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b)._PC = if c then a._PC else b._PC := by split <;> rfl
theorem dite_rPC {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h)._PC = if h : c then (a h)._PC else (b h)._PC := by split <;> rfl
theorem ite_rbank_BitVec_64 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_64 = if c then a.bank_BitVec_64 else b.bank_BitVec_64 := by split <;> rfl
theorem dite_rbank_BitVec_64 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_64 = if h : c then (a h).bank_BitVec_64 else (b h).bank_BitVec_64 := by split <;> rfl
theorem ite_rbank_BitVec_32 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_32 = if c then a.bank_BitVec_32 else b.bank_BitVec_32 := by split <;> rfl
theorem dite_rbank_BitVec_32 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_32 = if h : c then (a h).bank_BitVec_32 else (b h).bank_BitVec_32 := by split <;> rfl
theorem ite_rbank_Int {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Int = if c then a.bank_Int else b.bank_Int := by split <;> rfl
theorem dite_rbank_Int {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Int = if h : c then (a h).bank_Int else (b h).bank_Int := by split <;> rfl
theorem ite_rShouldAdvanceSS {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).ShouldAdvanceSS = if c then a.ShouldAdvanceSS else b.ShouldAdvanceSS := by split <;> rfl
theorem dite_rShouldAdvanceSS {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).ShouldAdvanceSS = if h : c then (a h).ShouldAdvanceSS else (b h).ShouldAdvanceSS := by split <;> rfl
theorem ite_rShouldAdvanceIT {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).ShouldAdvanceIT = if c then a.ShouldAdvanceIT else b.ShouldAdvanceIT := by split <;> rfl
theorem dite_rShouldAdvanceIT {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).ShouldAdvanceIT = if h : c then (a h).ShouldAdvanceIT else (b h).ShouldAdvanceIT := by split <;> rfl
theorem ite_rThisInstrEnc {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).__ThisInstrEnc = if c then a.__ThisInstrEnc else b.__ThisInstrEnc := by split <;> rfl
theorem dite_rThisInstrEnc {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).__ThisInstrEnc = if h : c then (a h).__ThisInstrEnc else (b h).__ThisInstrEnc := by split <;> rfl
theorem ite_rBranchtypetaken {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).Branchtypetaken = if c then a.Branchtypetaken else b.Branchtypetaken := by split <;> rfl
theorem dite_rBranchtypetaken {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).Branchtypetaken = if h : c then (a h).Branchtypetaken else (b h).Branchtypetaken := by split <;> rfl
theorem ite_remulator_termination_opcode {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).__emulator_termination_opcode = if c then a.__emulator_termination_opcode else b.__emulator_termination_opcode := by split <;> rfl
theorem dite_remulator_termination_opcode {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).__emulator_termination_opcode = if h : c then (a h).__emulator_termination_opcode else (b h).__emulator_termination_opcode := by split <;> rfl
theorem ite_rbank_BitVec_128 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_128 = if c then a.bank_BitVec_128 else b.bank_BitVec_128 := by split <;> rfl
theorem dite_rbank_BitVec_128 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_128 = if h : c then (a h).bank_BitVec_128 else (b h).bank_BitVec_128 := by split <;> rfl
theorem ite_pD {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).D = if c then a.D else b.D := by split <;> rfl
theorem dite_pD {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).D = if h : c then (a h).D else (b h).D := by split <;> rfl
theorem ite_pA {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).A = if c then a.A else b.A := by split <;> rfl
theorem dite_pA {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).A = if h : c then (a h).A else (b h).A := by split <;> rfl
theorem ite_pI {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).I = if c then a.I else b.I := by split <;> rfl
theorem dite_pI {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).I = if h : c then (a h).I else (b h).I := by split <;> rfl
theorem ite_pF {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).F = if c then a.F else b.F := by split <;> rfl
theorem dite_pF {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).F = if h : c then (a h).F else (b h).F := by split <;> rfl
theorem ite_pEXLOCK {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).EXLOCK = if c then a.EXLOCK else b.EXLOCK := by split <;> rfl
theorem dite_pEXLOCK {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).EXLOCK = if h : c then (a h).EXLOCK else (b h).EXLOCK := by split <;> rfl
theorem ite_pPAN {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).PAN = if c then a.PAN else b.PAN := by split <;> rfl
theorem dite_pPAN {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).PAN = if h : c then (a h).PAN else (b h).PAN := by split <;> rfl
theorem ite_pUAO {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).UAO = if c then a.UAO else b.UAO := by split <;> rfl
theorem dite_pUAO {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).UAO = if h : c then (a h).UAO else (b h).UAO := by split <;> rfl
theorem ite_pDIT {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).DIT = if c then a.DIT else b.DIT := by split <;> rfl
theorem dite_pDIT {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).DIT = if h : c then (a h).DIT else (b h).DIT := by split <;> rfl
theorem ite_pTCO {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).TCO = if c then a.TCO else b.TCO := by split <;> rfl
theorem dite_pTCO {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).TCO = if h : c then (a h).TCO else (b h).TCO := by split <;> rfl
theorem ite_pPM {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).PM = if c then a.PM else b.PM := by split <;> rfl
theorem dite_pPM {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).PM = if h : c then (a h).PM else (b h).PM := by split <;> rfl
theorem ite_pPPEND {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).PPEND = if c then a.PPEND else b.PPEND := by split <;> rfl
theorem dite_pPPEND {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).PPEND = if h : c then (a h).PPEND else (b h).PPEND := by split <;> rfl
theorem ite_pBTYPE {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).BTYPE = if c then a.BTYPE else b.BTYPE := by split <;> rfl
theorem dite_pBTYPE {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).BTYPE = if h : c then (a h).BTYPE else (b h).BTYPE := by split <;> rfl
theorem ite_pZA {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).ZA = if c then a.ZA else b.ZA := by split <;> rfl
theorem dite_pZA {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).ZA = if h : c then (a h).ZA else (b h).ZA := by split <;> rfl
theorem ite_pSM {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).SM = if c then a.SM else b.SM := by split <;> rfl
theorem dite_pSM {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).SM = if h : c then (a h).SM else (b h).SM := by split <;> rfl
theorem ite_pALLINT {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).ALLINT = if c then a.ALLINT else b.ALLINT := by split <;> rfl
theorem dite_pALLINT {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).ALLINT = if h : c then (a h).ALLINT else (b h).ALLINT := by split <;> rfl
theorem ite_pSS {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).SS = if c then a.SS else b.SS := by split <;> rfl
theorem dite_pSS {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).SS = if h : c then (a h).SS else (b h).SS := by split <;> rfl
theorem ite_pIL {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).IL = if c then a.IL else b.IL := by split <;> rfl
theorem dite_pIL {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).IL = if h : c then (a h).IL else (b h).IL := by split <;> rfl
theorem ite_pEL {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).EL = if c then a.EL else b.EL := by split <;> rfl
theorem dite_pEL {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).EL = if h : c then (a h).EL else (b h).EL := by split <;> rfl
theorem ite_pnRW {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).nRW = if c then a.nRW else b.nRW := by split <;> rfl
theorem dite_pnRW {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).nRW = if h : c then (a h).nRW else (b h).nRW := by split <;> rfl
theorem ite_pSP {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).SP = if c then a.SP else b.SP := by split <;> rfl
theorem dite_pSP {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).SP = if h : c then (a h).SP else (b h).SP := by split <;> rfl
theorem ite_pQ {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).Q = if c then a.Q else b.Q := by split <;> rfl
theorem dite_pQ {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).Q = if h : c then (a h).Q else (b h).Q := by split <;> rfl
theorem ite_pGE {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).GE = if c then a.GE else b.GE := by split <;> rfl
theorem dite_pGE {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).GE = if h : c then (a h).GE else (b h).GE := by split <;> rfl
theorem ite_pSSBS {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).SSBS = if c then a.SSBS else b.SSBS := by split <;> rfl
theorem dite_pSSBS {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).SSBS = if h : c then (a h).SSBS else (b h).SSBS := by split <;> rfl
theorem ite_pIT {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).IT = if c then a.IT else b.IT := by split <;> rfl
theorem dite_pIT {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).IT = if h : c then (a h).IT else (b h).IT := by split <;> rfl
theorem ite_pJ {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).J = if c then a.J else b.J := by split <;> rfl
theorem dite_pJ {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).J = if h : c then (a h).J else (b h).J := by split <;> rfl
theorem ite_pT {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).T = if c then a.T else b.T := by split <;> rfl
theorem dite_pT {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).T = if h : c then (a h).T else (b h).T := by split <;> rfl
theorem ite_pE {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).E = if c then a.E else b.E := by split <;> rfl
theorem dite_pE {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).E = if h : c then (a h).E else (b h).E := by split <;> rfl
theorem ite_pM {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).M = if c then a.M else b.M := by split <;> rfl
theorem dite_pM {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).M = if h : c then (a h).M else (b h).M := by split <;> rfl

theorem ite_rgpr {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).gpr = if c then a.gpr else b.gpr := by split <;> rfl
theorem dite_rgpr {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).gpr = if h : c then (a h).gpr else (b h).gpr := by split <;> rfl
theorem ite_rSP_EL0 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).SP_EL0 = if c then a.SP_EL0 else b.SP_EL0 := by split <;> rfl
theorem dite_rSP_EL0 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).SP_EL0 = if h : c then (a h).SP_EL0 else (b h).SP_EL0 := by split <;> rfl
theorem ite_rZ {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b)._Z = if c then a._Z else b._Z := by split <;> rfl
theorem dite_rZ {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h)._Z = if h : c then (a h)._Z else (b h)._Z := by split <;> rfl
theorem ite_pN {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).N = if c then a.N else b.N := by split <;> rfl
theorem dite_pN {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).N = if h : c then (a h).N else (b h).N := by split <;> rfl
theorem ite_pZ {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).Z = if c then a.Z else b.Z := by split <;> rfl
theorem dite_pZ {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).Z = if h : c then (a h).Z else (b h).Z := by split <;> rfl
theorem ite_pC {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).C = if c then a.C else b.C := by split <;> rfl
theorem dite_pC {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).C = if h : c then (a h).C else (b h).C := by split <;> rfl
theorem ite_pV {c : Prop} [Decidable c] (a b : ProcState) : (if c then a else b).V = if c then a.V else b.V := by split <;> rfl
theorem dite_pV {c : Prop} [Decidable c] (a : c → ProcState) (b : ¬c → ProcState) :
    (if h : c then a h else b h).V = if h : c then (a h).V else (b h).V := by split <;> rfl
theorem ite_rPMEVCNTSVR_EL1 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).PMEVCNTSVR_EL1 = if c then a.PMEVCNTSVR_EL1 else b.PMEVCNTSVR_EL1 := by split <;> rfl
theorem dite_rPMEVCNTSVR_EL1 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).PMEVCNTSVR_EL1 = if h : c then (a h).PMEVCNTSVR_EL1 else (b h).PMEVCNTSVR_EL1 := by split <;> rfl
theorem ite_rSPESampleCounter {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).SPESampleCounter = if c then a.SPESampleCounter else b.SPESampleCounter := by split <;> rfl
theorem dite_rSPESampleCounter {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).SPESampleCounter = if h : c then (a h).SPESampleCounter else (b h).SPESampleCounter := by split <;> rfl
theorem ite_rSPERecordData {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).SPERecordData = if c then a.SPERecordData else b.SPERecordData := by split <;> rfl
theorem dite_rSPERecordData {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).SPERecordData = if h : c then (a h).SPERecordData else (b h).SPERecordData := by split <;> rfl
theorem ite_rSP_EL3 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).SP_EL3 = if c then a.SP_EL3 else b.SP_EL3 := by split <;> rfl
theorem dite_rSP_EL3 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).SP_EL3 = if h : c then (a h).SP_EL3 else (b h).SP_EL3 := by split <;> rfl
theorem ite_rSP_EL2 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).SP_EL2 = if c then a.SP_EL2 else b.SP_EL2 := by split <;> rfl
theorem dite_rSP_EL2 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).SP_EL2 = if h : c then (a h).SP_EL2 else (b h).SP_EL2 := by split <;> rfl
theorem ite_rSP_EL1 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).SP_EL1 = if c then a.SP_EL1 else b.SP_EL1 := by split <;> rfl
theorem dite_rSP_EL1 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).SP_EL1 = if h : c then (a h).SP_EL1 else (b h).SP_EL1 := by split <;> rfl
theorem ite_rmpam_vpmr_max {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).__mpam_vpmr_max = if c then a.__mpam_vpmr_max else b.__mpam_vpmr_max := by split <;> rfl
theorem dite_rmpam_vpmr_max {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).__mpam_vpmr_max = if h : c then (a h).__mpam_vpmr_max else (b h).__mpam_vpmr_max := by split <;> rfl
theorem ite_rSPE_LFSR {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).__SPE_LFSR = if c then a.__SPE_LFSR else b.__SPE_LFSR := by split <;> rfl
theorem dite_rSPE_LFSR {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).__SPE_LFSR = if h : c then (a h).__SPE_LFSR else (b h).__SPE_LFSR := by split <;> rfl
theorem ite_rSPESampleOpType {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).SPESampleOpType = if c then a.SPESampleOpType else b.SPESampleOpType := by split <;> rfl
theorem dite_rSPESampleOpType {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).SPESampleOpType = if h : c then (a h).SPESampleOpType else (b h).SPESampleOpType := by split <;> rfl
theorem ite_rTSTATE {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).TSTATE = if c then a.TSTATE else b.TSTATE := by split <;> rfl
theorem dite_rTSTATE {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).TSTATE = if h : c then (a h).TSTATE else (b h).TSTATE := by split <;> rfl
theorem ite_rFPSR {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).FPSR = if c then a.FPSR else b.FPSR := by split <;> rfl
theorem dite_rFPSR {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).FPSR = if h : c then (a h).FPSR else (b h).FPSR := by split <;> rfl
theorem ite_rFPCR {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).FPCR = if c then a.FPCR else b.FPCR := by split <;> rfl
theorem dite_rFPCR {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).FPCR = if h : c then (a h).FPCR else (b h).FPCR := by split <;> rfl
theorem ite_rZT0 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b)._ZT0 = if c then a._ZT0 else b._ZT0 := by split <;> rfl
theorem dite_rZT0 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h)._ZT0 = if h : c then (a h)._ZT0 else (b h)._ZT0 := by split <;> rfl
theorem ite_rZA {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b)._ZA = if c then a._ZA else b._ZA := by split <;> rfl
theorem dite_rZA {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h)._ZA = if h : c then (a h)._ZA else (b h)._ZA := by split <;> rfl
theorem ite_rFFR {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b)._FFR = if c then a._FFR else b._FFR := by split <;> rfl
theorem dite_rFFR {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h)._FFR = if h : c then (a h)._FFR else (b h)._FFR := by split <;> rfl
theorem ite_rP {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b)._P = if c then a._P else b._P := by split <;> rfl
theorem dite_rP {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h)._P = if h : c then (a h)._P else (b h)._P := by split <;> rfl
theorem ite_rBTypeCompatible {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).BTypeCompatible = if c then a.BTypeCompatible else b.BTypeCompatible := by split <;> rfl
theorem dite_rBTypeCompatible {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).BTypeCompatible = if h : c then (a h).BTypeCompatible else (b h).BTypeCompatible := by split <;> rfl
theorem ite_rRC {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).RC = if c then a.RC else b.RC := by split <;> rfl
theorem dite_rRC {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).RC = if h : c then (a h).RC else (b h).RC := by split <;> rfl
theorem ite_rPhysicalCount {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).PhysicalCount = if c then a.PhysicalCount else b.PhysicalCount := by split <;> rfl
theorem dite_rPhysicalCount {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).PhysicalCount = if h : c then (a h).PhysicalCount else (b h).PhysicalCount := by split <;> rfl
theorem ite_rPMULastThresholdValue {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).PMULastThresholdValue = if c then a.PMULastThresholdValue else b.PMULastThresholdValue := by split <;> rfl
theorem dite_rPMULastThresholdValue {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).PMULastThresholdValue = if h : c then (a h).PMULastThresholdValue else (b h).PMULastThresholdValue := by split <;> rfl
theorem ite_rPMUEventAccumulator {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).PMUEventAccumulator = if c then a.PMUEventAccumulator else b.PMUEventAccumulator := by split <;> rfl
theorem dite_rPMUEventAccumulator {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).PMUEventAccumulator = if h : c then (a h).PMUEventAccumulator else (b h).PMUEventAccumulator := by split <;> rfl
theorem ite_rVariantImplemented {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).VariantImplemented = if c then a.VariantImplemented else b.VariantImplemented := by split <;> rfl
theorem dite_rVariantImplemented {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).VariantImplemented = if h : c then (a h).VariantImplemented else (b h).VariantImplemented := by split <;> rfl
theorem ite_rbank_Vector_BitVec_32_16 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_BitVec_32_16 = if c then a.bank_Vector_BitVec_32_16 else b.bank_Vector_BitVec_32_16 := by split <;> rfl
theorem dite_rbank_Vector_BitVec_32_16 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_BitVec_32_16 = if h : c then (a h).bank_Vector_BitVec_32_16 else (b h).bank_Vector_BitVec_32_16 := by split <;> rfl
theorem ite_rbank_Vector_BitVec_32_4 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_BitVec_32_4 = if c then a.bank_Vector_BitVec_32_4 else b.bank_Vector_BitVec_32_4 := by split <;> rfl
theorem dite_rbank_Vector_BitVec_32_4 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_BitVec_32_4 = if h : c then (a h).bank_Vector_BitVec_32_4 else (b h).bank_Vector_BitVec_32_4 := by split <;> rfl
theorem ite_rbank_Vector_BitVec_64_32 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_BitVec_64_32 = if c then a.bank_Vector_BitVec_64_32 else b.bank_Vector_BitVec_64_32 := by split <;> rfl
theorem dite_rbank_Vector_BitVec_64_32 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_BitVec_64_32 = if h : c then (a h).bank_Vector_BitVec_64_32 else (b h).bank_Vector_BitVec_64_32 := by split <;> rfl
theorem ite_rbank_Vector_BitVec_64_16 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_BitVec_64_16 = if c then a.bank_Vector_BitVec_64_16 else b.bank_Vector_BitVec_64_16 := by split <;> rfl
theorem dite_rbank_Vector_BitVec_64_16 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_BitVec_64_16 = if h : c then (a h).bank_Vector_BitVec_64_16 else (b h).bank_Vector_BitVec_64_16 := by split <;> rfl
theorem ite_rbank_Vector_BitVec_64_4 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_BitVec_64_4 = if c then a.bank_Vector_BitVec_64_4 else b.bank_Vector_BitVec_64_4 := by split <;> rfl
theorem dite_rbank_Vector_BitVec_64_4 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_BitVec_64_4 = if h : c then (a h).bank_Vector_BitVec_64_4 else (b h).bank_Vector_BitVec_64_4 := by split <;> rfl
theorem ite_rbank_Vector_BitVec_32_31 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_BitVec_32_31 = if c then a.bank_Vector_BitVec_32_31 else b.bank_Vector_BitVec_32_31 := by split <;> rfl
theorem dite_rbank_Vector_BitVec_32_31 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_BitVec_32_31 = if h : c then (a h).bank_Vector_BitVec_32_31 else (b h).bank_Vector_BitVec_32_31 := by split <;> rfl
theorem ite_rbank_BitVec_1 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_1 = if c then a.bank_BitVec_1 else b.bank_BitVec_1 := by split <;> rfl
theorem dite_rbank_BitVec_1 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_1 = if h : c then (a h).bank_BitVec_1 else (b h).bank_BitVec_1 := by split <;> rfl
theorem ite_rbank_BitVec_56 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_56 = if c then a.bank_BitVec_56 else b.bank_BitVec_56 := by split <;> rfl
theorem dite_rbank_BitVec_56 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_56 = if h : c then (a h).bank_BitVec_56 else (b h).bank_BitVec_56 := by split <;> rfl
theorem ite_rbank_BitVec_16 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_16 = if c then a.bank_BitVec_16 else b.bank_BitVec_16 := by split <;> rfl
theorem dite_rbank_BitVec_16 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_16 = if h : c then (a h).bank_BitVec_16 else (b h).bank_BitVec_16 := by split <;> rfl
theorem ite_rbank_BitVec_4 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_4 = if c then a.bank_BitVec_4 else b.bank_BitVec_4 := by split <;> rfl
theorem dite_rbank_BitVec_4 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_4 = if h : c then (a h).bank_BitVec_4 else (b h).bank_BitVec_4 := by split <;> rfl
theorem ite_rbank_Vector_Bool_32 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_Bool_32 = if c then a.bank_Vector_Bool_32 else b.bank_Vector_Bool_32 := by split <;> rfl
theorem dite_rbank_Vector_Bool_32 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_Bool_32 = if h : c then (a h).bank_Vector_Bool_32 else (b h).bank_Vector_Bool_32 := by split <;> rfl
theorem ite_rbank_Vector_BitVec_64_64 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_BitVec_64_64 = if c then a.bank_Vector_BitVec_64_64 else b.bank_Vector_BitVec_64_64 := by split <;> rfl
theorem dite_rbank_Vector_BitVec_64_64 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_BitVec_64_64 = if h : c then (a h).bank_Vector_BitVec_64_64 else (b h).bank_Vector_BitVec_64_64 := by split <;> rfl
theorem ite_rbank_Option_InterruptID {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Option_InterruptID = if c then a.bank_Option_InterruptID else b.bank_Option_InterruptID := by split <;> rfl
theorem dite_rbank_Option_InterruptID {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Option_InterruptID = if h : c then (a h).bank_Option_InterruptID else (b h).bank_Option_InterruptID := by split <;> rfl
theorem ite_rbank_BitVec_8 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_8 = if c then a.bank_BitVec_8 else b.bank_BitVec_8 := by split <;> rfl
theorem dite_rbank_BitVec_8 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_8 = if h : c then (a h).bank_BitVec_8 else (b h).bank_BitVec_8 := by split <;> rfl
theorem ite_rbank_BitVec_2 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_BitVec_2 = if c then a.bank_BitVec_2 else b.bank_BitVec_2 := by split <;> rfl
theorem dite_rbank_BitVec_2 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_BitVec_2 = if h : c then (a h).bank_BitVec_2 else (b h).bank_BitVec_2 := by split <;> rfl
theorem ite_rbank_Vector_BitVec_64_7 {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Vector_BitVec_64_7 = if c then a.bank_Vector_BitVec_64_7 else b.bank_Vector_BitVec_64_7 := by split <;> rfl
theorem dite_rbank_Vector_BitVec_64_7 {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Vector_BitVec_64_7 = if h : c then (a h).bank_Vector_BitVec_64_7 else (b h).bank_Vector_BitVec_64_7 := by split <;> rfl
theorem ite_rbank_Signal {c : Prop} [Decidable c] (a b : Regs) : (if c then a else b).bank_Signal = if c then a.bank_Signal else b.bank_Signal := by split <;> rfl
theorem dite_rbank_Signal {c : Prop} [Decidable c] (a : c → Regs) (b : ¬c → Regs) :
    (if h : c then a h else b h).bank_Signal = if h : c then (a h).bank_Signal else (b h).bank_Signal := by split <;> rfl
theorem natcast31 : ((31 : Nat) : Int) = 31 := rfl

#print axioms dite_ok
#print axioms sw_join1
#print axioms ok_of_root
#print axioms frame_of_root
#print axioms val_of_root
end ArmBridge.RootFrame
