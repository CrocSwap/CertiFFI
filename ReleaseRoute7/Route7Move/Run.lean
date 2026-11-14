-- Route 7 breadth: memmove prefix (CBZ x2; CMP x0,x1; B.EQ; B.LO; MOV | ADD,ADD), the four paths
-- (empty / same / forward / backward), the loop inductions and the complete run over EnvM in EXACTLY
-- Schedule.moveSteps (movePath d s n) n steps.
import Route7Move.Bwd
import Route7Move.Steps
import Route7StepsE.Move
import Route7Copy.Run
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open HeapV2StepCerts.RegBind (rk)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option Elab.async false

namespace Route7Move
open ArmCertLoop ArmCertLoop.ContractDraft

/-! ## Schedule facts -/

theorem budget_ge2 (c : Context) : 2 ≤ c.budget := by
  unfold Context.budget; generalize c.path = p; cases p <;> simp [Schedule.moveSteps] <;> omega

theorem path_empty (c : Context) (zero : c.n = 0) : c.path = .empty := by
  simp only [Context.path, movePath, if_pos zero]

theorem path_same (c : Context) (nz : c.n ≠ 0) (same : c.d = c.s) : c.path = .same := by
  simp only [Context.path, movePath, if_neg nz, if_pos same]

theorem offset_at (c : Context) (p : Schedule.MovePath) (hp : c.path = p) (k : Nat) (hk : k ≠ Schedule.moveSteps p c.n) :
    offset c k = BitVec.ofNat 64 (Generated.armcert_memmove_entry + Schedule.moveWordOffset p c.n k) := by
  simp only [offset, Schedule.nativeOffset, Context.budget, hp]
  rw [if_neg hk]

theorem offset_zero (c : Context) : offset c 0 = 484#64 := by
  have h := budget_ge2 c
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg (by omega)]
  have : Schedule.moveWordOffset c.path c.n 0 = 0 := by
    generalize c.path = p; cases p <;> simp [Schedule.moveWordOffset]
  rw [this]; rfl

theorem offset_one (c : Context) : offset c 1 = BitVec.ofNat 64 (484 + if c.n = 0 then 48 else 4) := by
  have h := budget_ge2 c
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg (by omega)]
  simp only [Context.path, movePath, Generated.armcert_memmove_entry]
  by_cases z : c.n = 0
  · simp [z, Schedule.moveWordOffset]
  · by_cases e : c.d = c.s
    · simp [z, e, Schedule.moveWordOffset]
    · by_cases l : c.d.toNat < c.s.toNat <;> simp [z, e, l, Schedule.moveWordOffset]

theorem offset_two (c : Context) (nz : c.n ≠ 0) : offset c 2 = 492#64 := by
  have bound : 2 < c.budget := by
    unfold Context.budget; simp only [Context.path, movePath, if_neg nz]
    by_cases e : c.d = c.s
    · simp [e, Schedule.moveSteps]
    · by_cases l : c.d.toNat < c.s.toNat <;> simp [e, l, Schedule.moveSteps] <;> omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg (by omega)]
  simp only [Context.path, movePath, if_neg nz]
  by_cases e : c.d = c.s
  · simp [e, Schedule.moveWordOffset]; rfl
  · by_cases l : c.d.toNat < c.s.toNat <;> simp [e, l, Schedule.moveWordOffset] <;> rfl

theorem offset_three (c : Context) (nz : c.n ≠ 0) :
    offset c 3 = BitVec.ofNat 64 (484 + if c.d = c.s then 48 else 12) := by
  have bound : 3 < c.budget := by
    unfold Context.budget; simp only [Context.path, movePath, if_neg nz]
    by_cases e : c.d = c.s
    · simp [e, Schedule.moveSteps]
    · by_cases l : c.d.toNat < c.s.toNat <;> simp [e, l, Schedule.moveSteps] <;> omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg (by omega)]
  simp only [Context.path, movePath, if_neg nz, Generated.armcert_memmove_entry]
  by_cases e : c.d = c.s
  · simp [e, Schedule.moveWordOffset]
  · by_cases l : c.d.toNat < c.s.toNat <;> simp [e, l, Schedule.moveWordOffset]

theorem budget_ge4 (c : Context) (nz : c.n ≠ 0) : 4 ≤ c.budget := by
  unfold Context.budget
  simp only [Context.path, movePath, if_neg nz]
  by_cases e : c.d = c.s
  · simp [e, Schedule.moveSteps]
  · by_cases l : c.d.toNat < c.s.toNat <;> simp [e, l, Schedule.moveSteps] <;> omega

/-- A zero-draw step advances EnvM at any index (movePast is monotone). -/
theorem advance0_m (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat)
    (x fin : NativeState) (env : EnvM c catalogue entry k x)
    (core : ReleaseProfile.DefaultCurrent.CurrentInv c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
      (offset c) c.budget (k + 1) catalogue fin)
    (choice : NativeMteTagCheck.ChoiceDelta x fin 0) : EnvM c catalogue entry (k + 1) fin :=
  ReleaseProfile.DefaultRuntime.InvG.advance env core True.intro ⟨0, choice, Nat.le_refl 0⟩
    (by rw [movePast_succ]; split <;> omega)

/-! ## Register / flag facts -/

theorem flags_gpr (before after : NativeState) (fl : ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd)
    (holds : ArmCertValue.VHolds [] (some fl) before after) : after.regs.gpr = before.regs.gpr := by
  apply Vector.ext
  intro i bounded
  exact holds.1 (.x ⟨i, bounded⟩)

theorem flags_sp (before after : NativeState) (fl : ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd)
    (holds : ArmCertValue.VHolds [] (some fl) before after) : after.regs.SP_EL0 = before.regs.SP_EL0 := holds.1 .sp

theorem addShift_gpr (Rd Rn Rm : BitVec 5) (before after : NativeState)
    (holds : ArmCertValue.VHolds (ArmCertValue.R14.AddShift64.upd Rd Rn Rm) none before after) :
    after.regs.gpr = before.regs.gpr.set (rk Rd).val (before.regs.gpr[(rk Rn).val] + before.regs.gpr[(rk Rm).val]) ∧
      after.regs.SP_EL0 = before.regs.SP_EL0 := by
  let value : ArmCertValue.VUpd := ⟨.add, [.reg (.x (rk Rn)), .reg (.x (rk Rm))]⟩
  have gpr := ValueFacts.single_gpr (rk Rd) value none before after holds
  exact ⟨gpr, ValueFacts.single_sp (rk Rd) value none before after holds⟩

theorem setWidth1_inj {a b : BitVec 1} (h : a.setWidth 64 = b.setWidth 64) : a = b := by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at e
  have ha := a.isLt
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e
  exact e

/-- A flag-preserving step (VHolds _ none) keeps every B.cond condition. -/
theorem bcond_keep (cond : BitVec 4) (us : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (before after : NativeState) (holds : ArmCertValue.VHolds us none before after) :
    Crypto.BcondCore.bcondC cond after.regs ↔ Crypto.BcondCore.bcondC cond before.regs := by
  have hN := setWidth1_inj (holds.2 0)
  have hZ := setWidth1_inj (holds.2 1)
  have hC := setWidth1_inj (holds.2 2)
  have hV := setWidth1_inj (holds.2 3)
  simp only [Crypto.BcondCore.bcondC, hN, hZ, hC, hV]

theorem cbz_taken_m (x : NativeState) (h : x.regs.gpr[2].toNat = 0) : Crypto.CruxCbz.cbzC 1#1 2#5 x :=
  (Route7Copy.cbz_cond_iff x).2 (BitVec.eq_of_toNat_eq h)

theorem cbz_not_m (x : NativeState) (h : x.regs.gpr[2].toNat ≠ 0) : ¬ Crypto.CruxCbz.cbzC 1#1 2#5 x := by
  intro cond
  apply h
  exact congrArg BitVec.toNat ((Route7Copy.cbz_cond_iff x).1 cond)

/-! ## Shared prefix steps -/

attribute [local instance 10] Classical.propDecidable in
/-- k = 0: CBZ x2, 532 (taken iff n = 0). -/
theorem step_cbz (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (counter : entry.regs.gpr[2].toNat = c.n) (env : EnvM c catalogue entry 0 entry) :
    ∃ a, modelStep real entry = .ok () a ∧ EnvM c catalogue entry 1 a ∧ a.mem = entry.mem ∧
      a.regs.gpr = entry.regs.gpr ∧ a.regs.SP_EL0 = entry.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} entry.regs a.regs ∧
      StepEvents.EvShape c.spec c.mapping [] entry a := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyCbz.W 2#5 12#19) entry := by
    exact fetch_index_m c catalogue entry 0 16 entry env (by decide) (by rw [env.core.v1.pc, offset_zero]; rfl)
  have target : entry.regs._PC + sign_extend (12#19 ++ 0#2) 64 = c.base + 532#64 := by
    change entry.regs._PC + 48#64 = c.base + 532#64
    rw [env.core.v1.pc, offset_zero]
    bv_omega
  have low : (entry.regs._PC + sign_extend (12#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [target]
    have := c.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have placed : (if Crypto.CruxCbz.cbzC 1#1 2#5 entry then entry.regs._PC + sign_extend (12#19 ++ 0#2) 64
      else entry.regs._PC + 4#64) = c.base + offset c (0 + 1) := by
    rw [offset_one]
    by_cases zero : c.n = 0
    · rw [if_pos (cbz_taken_m entry (by omega)), target, if_pos zero]
    · rw [if_neg (cbz_not_m entry (by omega)), env.core.v1.pc, offset_zero, if_neg zero]
      change c.base + 484#64 + 4#64 = c.base + 488#64
      bv_omega
  obtain ⟨a, run, core1, holds, memory, _, _, _, frame, choice, ev⟩ :=
    Route7Steps.cbz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget 0 catalogue (by have := budget_ge2 c; omega) c.page
      (by rw [offset_zero]; decide) 2#5 12#19 entry env.core nodup low _ rfl placed fetch
  exact ⟨a, run, advance0_m c catalogue entry 0 entry a env core1 choice, memory,
    ValueFacts.nil_gpr entry a holds, ValueFacts.nil_sp entry a holds, frame, ev⟩

/-- k = 1: CMP x0, x1 (n ≠ 0). -/
theorem step_cmp (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry a : NativeState) (nz : c.n ≠ 0)
    (env : EnvM c catalogue entry 1 a) :
    ∃ b, modelStep real a = .ok () b ∧ EnvM c catalogue entry 2 b ∧
      ArmCertValue.VHolds [] (some (ArmCertValue.R14.SubsShift64ZRd.fl 0#5 1#5)) a b ∧ b.mem = a.mem ∧
      b.regs.gpr = a.regs.gpr ∧ b.regs.SP_EL0 = a.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} a.regs b.regs ∧
      StepEvents.EvShape c.spec c.mapping [] a b := by
  have pc : a.regs._PC = c.base + 488#64 := by rw [env.core.v1.pc, offset_one, if_neg nz]
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.SubsShift64ZRd.selected 0#5 0#6 1#5) a := by
    exact fetch_index_m c catalogue entry 1 17 a env (by decide) (by rw [pc]; rfl)
  have placed : a.regs._PC + 4#64 = c.base + offset c (1 + 1) := by
    rw [pc, offset_two c nz]; bv_omega
  obtain ⟨b, run, core2, holds, memory, _, _, _, frame, choice, ev⟩ :=
    subsShift64ZRdE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget 1 catalogue (by have := budget_ge2 c; omega)
      c.page (by rw [offset_one, if_neg nz]; decide) 0#5 1#5 (by decide) (by decide) (by decide) a env.core nodup placed fetch
  exact ⟨b, run, advance0_m c catalogue entry 1 a b env core2 choice, holds, memory,
    flags_gpr a b _ holds, flags_sp a b _ holds, frame, ev⟩

attribute [local instance 10] Classical.propDecidable in
/-- k = 2: B.EQ 532 (taken iff d = s, by the CMP flags). -/
theorem step_beq (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry a b : NativeState) (nz : c.n ≠ 0)
    (d0 : a.regs.gpr[0] = c.d) (s1 : a.regs.gpr[1] = c.s)
    (cmp : ArmCertValue.VHolds [] (some (ArmCertValue.R14.SubsShift64ZRd.fl 0#5 1#5)) a b)
    (env : EnvM c catalogue entry 2 b) :
    ∃ e, modelStep real b = .ok () e ∧ EnvM c catalogue entry 3 e ∧ ArmCertValue.VHolds [] none b e ∧ e.mem = b.mem ∧
      e.regs.gpr = b.regs.gpr ∧ e.regs.SP_EL0 = b.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} b.regs e.regs ∧
      StepEvents.EvShape c.spec c.mapping [] b e := by
  have pc : b.regs._PC = c.base + 492#64 := by rw [env.core.v1.pc, offset_two c nz]
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (ReleaseProfile.DefaultRuntimeBcondEventTail.W 0#4 10#19) b := by
    exact fetch_index_m c catalogue entry 2 18 b env (by decide) (by rw [pc]; rfl)
  have target : b.regs._PC + sign_extend (10#19 +++ 0#2) 64 = c.base + 532#64 := by
    rw [pc]; change c.base + 492#64 + 40#64 = c.base + 532#64; bv_omega
  have low : (b.regs._PC + sign_extend (10#19 +++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [target]; have := c.low; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have iff : Crypto.BcondCore.bcondC 0#4 b.regs ↔ c.d = c.s := by
    rw [cmp_eq a b cmp, d0, s1]
  have placed : (if Crypto.BcondCore.bcondC 0#4 b.regs then b.regs._PC + sign_extend (10#19 +++ 0#2) 64
      else b.regs._PC + 4#64) = c.base + offset c (2 + 1) := by
    rw [offset_three c nz]
    by_cases same : c.d = c.s
    · rw [if_pos (iff.2 same), target, if_pos same]
    · rw [if_neg (fun h => same (iff.1 h)), pc, if_neg same]
      change c.base + 492#64 + 4#64 = c.base + 496#64
      bv_omega
  have room : 2 < c.budget := by have := budget_ge4 c nz; omega
  obtain ⟨e, run, core3, holds, memory, _, _, _, frame, choice, ev⟩ :=
    bcondE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget 2 catalogue room c.page (by rw [offset_two c nz]; decide) 0#4 10#19 (by decide)
      b env.core nodup low _ placed rfl fetch
  exact ⟨e, run, advance0_m c catalogue entry 2 b e env core3 choice, holds, memory,
    ValueFacts.nil_gpr b e holds, ValueFacts.nil_sp b e holds, frame, ev⟩

/-- RET at word 532 (image 28) from step k with offset k = 532 (empty: k = 1; same: k = 3). -/
theorem step_ret532 (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState) (k : Nat)
    (room : k < c.budget) (off : offset c k = 532#64) (env : EnvM c catalogue entry k x)
    (link : x.regs.gpr[30] = c.returnPC) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._PC = c.returnPC ∧ fin.mem = x.mem ∧
      fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧
      StepEvents.EvShape c.spec c.mapping [] x fin := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) x := by
    exact fetch_index_m c catalogue entry k 28 x env (by decide) (by rw [env.core.v1.pc, off]; rfl)
  obtain ⟨fin, run, pc, holds, memory, _, _, _, kept, _, ev⟩ :=
    Route7Steps.retE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget k catalogue room c.page (by rw [off]; decide) 30#5 (by decide) x env.core nodup
      (by change x.regs.gpr[30].toNat < 2 ^ 55; rw [link]; have := c.returnLow; omega) fetch
  exact ⟨fin, run, pc.trans link, memory, ValueFacts.nil_gpr x fin holds, ValueFacts.nil_sp x fin holds, kept, ev⟩

/-! ## The paths -/

/-- Post for a run that touched no memory and left x0..x30 / SP as at entry (empty and same paths). -/
theorem post_untouched (c : Context) (entry fin : NativeState) (pc : fin.regs._PC = c.returnPC)
    (memory : fin.mem = entry.mem) (gpr : fin.regs.gpr = entry.regs.gpr) (sp : fin.regs.SP_EL0 = entry.regs.SP_EL0)
    (abi : NativeEntry.Effects.Frame {} entry.regs fin.regs) (dest : entry.regs.gpr[0] = c.d)
    (copy : ∀ i, i < c.n → readByte c.mapping fin (c.d + BitVec.ofNat 64 i) = readByte c.mapping entry (c.s + BitVec.ofNat 64 i)) :
    MovePost c.mapping c.d c.s c.returnPC c.n entry fin := by
  refine ⟨pc, ?_, copy, ?_, ?_, sp, LoopNative.MemoryFrame.vector abi rfl,
    LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩
  · change fin.regs.gpr[0] = c.d; rw [gpr]; exact dest
  · intro pa _; rw [memory]
  · intro r _; change fin.regs.gpr[r.val] = entry.regs.gpr[r.val]; rw [gpr]

theorem readByte_mem (mapping : BitVec 64 → Option Nat) (x y : NativeState) (h : x.mem = y.mem) (va : BitVec 64) :
    readByte mapping x va = readByte mapping y va := by
  simp only [readByte, h]

/-- n = 0: CBZ taken, RET. -/
theorem empty_m (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState) (zero : c.n = 0)
    (args : ContractDraft.Args c.d c.s c.returnPC c.n entry) (env : EnvM c catalogue entry 0 entry) :
    ∃ fin, Uget.Chain.modelRun real c.budget entry = .ok () fin ∧ MovePost c.mapping c.d c.s c.returnPC c.n entry fin ∧
      Route7Copy.Covered real (PcOkM c) c.budget entry ∧ Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) c.budget 0 entry := by
  obtain ⟨dest, _, counter, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[2].toNat = c.n at counter
  change entry.regs.gpr[30] = c.returnPC at link
  have cost : c.budget = 2 := by simp only [Context.budget, path_empty c zero, Schedule.moveSteps]
  obtain ⟨a, run0, env1, memory0, gpr0, sp0, frame0, ev0⟩ := step_cbz real c catalogue nodup entry counter env
  obtain ⟨fin, run1, pc, memory1, gpr1, sp1, frame1, ev1⟩ :=
    step_ret532 real c catalogue nodup entry a 1 (by omega) (by rw [offset_one, if_pos zero]) env1
      (by rw [gpr0]; exact link)
  have runFin : Uget.Chain.modelRun real 2 entry = .ok () fin := by simp only [Uget.Chain.modelRun, run0, run1]
  refine ⟨fin, ?_, post_untouched c entry fin pc (memory1.trans memory0) (gpr1.trans gpr0) (sp1.trans sp0)
    (frame0.trans frame1) dest (fun i room => by omega), ?_, ?_⟩
  · rw [cost]; exact runFin
  · rw [cost]
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with hm | hm | hm <;> subst hm
    · exact ⟨entry, rfl, pcOk_of_env_m c catalogue entry _ entry env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_m c catalogue entry _ a env1⟩
    · exact ⟨fin, runFin, Or.inl pc, CT1.Route7Word.imageWords_of_mem memory1 (pcOk_of_env_m c catalogue entry _ a env1).2⟩
  · -- trace (loops CT0): no data records
    rw [cost]
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with hj | hj <;> subst hj
    · refine ⟨entry, a, rfl, run0, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ entry env
      · rw [recs_empty c (path_empty c zero)]; exact ⟨ev0, frame0⟩
    · refine ⟨a, fin, by simp only [Uget.Chain.modelRun, run0], run1, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ a env1
      · rw [recs_empty c (path_empty c zero)]; exact ⟨ev1, frame1⟩


/-- n ≠ 0, d = s: CBZ, CMP, B.EQ taken, RET (nothing to move). -/
theorem same_m (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState) (nz : c.n ≠ 0) (same : c.d = c.s)
    (args : ContractDraft.Args c.d c.s c.returnPC c.n entry) (env : EnvM c catalogue entry 0 entry) :
    ∃ fin, Uget.Chain.modelRun real c.budget entry = .ok () fin ∧ MovePost c.mapping c.d c.s c.returnPC c.n entry fin ∧
      Route7Copy.Covered real (PcOkM c) c.budget entry ∧ Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) c.budget 0 entry := by
  obtain ⟨dest, source, counter, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[1] = c.s at source
  change entry.regs.gpr[2].toNat = c.n at counter
  change entry.regs.gpr[30] = c.returnPC at link
  have cost : c.budget = 4 := by simp only [Context.budget, path_same c nz same, Schedule.moveSteps]
  obtain ⟨a, run0, env1, memory0, gpr0, sp0, frame0, ev0⟩ := step_cbz real c catalogue nodup entry counter env
  obtain ⟨b, run1, env2, cmp, memory1, gpr1, sp1, frame1, ev1⟩ := step_cmp real c catalogue nodup entry a nz env1
  obtain ⟨e, run2, env3, _, memory2, gpr2, sp2, frame2, ev2⟩ :=
    step_beq real c catalogue nodup entry a b nz (by rw [gpr0]; exact dest) (by rw [gpr0]; exact source) cmp env2
  have gpr : e.regs.gpr = entry.regs.gpr := gpr2.trans (gpr1.trans gpr0)
  obtain ⟨fin, run3, pc, memory3, gpr3, sp3, frame3, ev3⟩ :=
    step_ret532 real c catalogue nodup entry e 3 (by omega) (by rw [offset_three c nz, if_pos same]) env3
      (by rw [gpr]; exact link)
  have memory : fin.mem = entry.mem := memory3.trans (memory2.trans (memory1.trans memory0))
  have runFin : Uget.Chain.modelRun real 4 entry = .ok () fin := by
    simp only [Uget.Chain.modelRun, run0, run1, run2, run3]
  refine ⟨fin, ?_, post_untouched c entry fin pc memory (gpr3.trans gpr) (sp3.trans (sp2.trans (sp1.trans sp0)))
    (((frame0.trans frame1).trans frame2).trans frame3) dest (fun i _ => by rw [same]; exact readByte_mem _ _ _ memory _), ?_, ?_⟩
  · rw [cost]; exact runFin
  · rw [cost]
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with hm | hm | hm | hm | hm <;> subst hm
    · exact ⟨entry, rfl, pcOk_of_env_m c catalogue entry _ entry env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_m c catalogue entry _ a env1⟩
    · exact ⟨b, by simp only [Uget.Chain.modelRun, run0, run1], pcOk_of_env_m c catalogue entry _ b env2⟩
    · exact ⟨e, by simp only [Uget.Chain.modelRun, run0, run1, run2], pcOk_of_env_m c catalogue entry _ e env3⟩
    · exact ⟨fin, runFin, Or.inl pc, CT1.Route7Word.imageWords_of_mem memory3 (pcOk_of_env_m c catalogue entry _ e env3).2⟩
  · -- trace (loops CT0): no data records
    rw [cost]
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with hj | hj | hj | hj <;> subst hj
    · refine ⟨entry, a, rfl, run0, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ entry env
      · rw [recs_same c (path_same c nz same)]; exact ⟨ev0, frame0⟩
    · refine ⟨a, b, by simp only [Uget.Chain.modelRun, run0], run1, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ a env1
      · rw [recs_same c (path_same c nz same)]; exact ⟨ev1, frame1⟩
    · refine ⟨b, e, by simp only [Uget.Chain.modelRun, run0, run1], run2, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ b env2
      · rw [recs_same c (path_same c nz same)]; exact ⟨ev2, frame2⟩
    · refine ⟨e, fin, by simp only [Uget.Chain.modelRun, run0, run1, run2], run3, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ e env3
      · rw [recs_same c (path_same c nz same)]; exact ⟨ev3, frame3⟩


attribute [local instance 10] Classical.propDecidable in
/-- Forward prefix (d <u s): CBZ, CMP, B.EQ, B.LO taken, MOV x3, x0 → HeaderF 0 at k = 5. -/
theorem enter_fwd (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (nz : c.n ≠ 0) (ne : c.d ≠ c.s) (lt : c.d.toNat < c.s.toNat)
    (args : ContractDraft.Args c.d c.s c.returnPC c.n entry) (env : EnvM c catalogue entry 0 entry) :
    ∃ x, Uget.Chain.modelRun real 5 entry = .ok () x ∧ HeaderF c catalogue entry 0 x ∧ Route7Copy.Covered real (PcOkM c) 5 entry ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) 5 0 entry := by
  have fwd := path_forward c nz ne lt
  obtain ⟨dest, source, counter, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[1] = c.s at source
  change entry.regs.gpr[2].toNat = c.n at counter
  change entry.regs.gpr[30] = c.returnPC at link
  obtain ⟨a, run0, env1, memory0, gpr0, sp0, frame0, ev0⟩ := step_cbz real c catalogue nodup entry counter env
  obtain ⟨b, run1, env2, cmp, memory1, gpr1, sp1, frame1, ev1⟩ := step_cmp real c catalogue nodup entry a nz env1
  obtain ⟨e, run2, env3, keep, memory2, gpr2, sp2, frame2, ev2⟩ :=
    step_beq real c catalogue nodup entry a b nz (by rw [gpr0]; exact dest) (by rw [gpr0]; exact source) cmp env2
  have gprE : e.regs.gpr = entry.regs.gpr := gpr2.trans (gpr1.trans gpr0)
  -- k = 3: B.LO 536 (taken: d <u s)
  have pc3 : e.regs._PC = c.base + 496#64 := by rw [env3.core.v1.pc, offset_three c nz, if_neg ne]
  have fetch3 : FetchObligations c.spec c.config c.rows c.mapping
      (ReleaseProfile.DefaultRuntimeBcondEventTail.W 3#4 10#19) e := by
    exact fetch_index_m c catalogue entry 3 19 e env3 (by decide) (by rw [pc3]; rfl)
  have target : e.regs._PC + sign_extend (10#19 +++ 0#2) 64 = c.base + 536#64 := by
    rw [pc3]; change c.base + 496#64 + 40#64 = c.base + 536#64; bv_omega
  have low : (e.regs._PC + sign_extend (10#19 +++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [target]; have := c.low; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have taken : Crypto.BcondCore.bcondC 3#4 e.regs := by
    rw [bcond_keep 3#4 [] b e keep, cmp_lo a b cmp, gpr0, dest, source]; exact lt
  have off4 : offset c 4 = 536#64 := by
    rw [offset_at c .forward fwd 4 (by simp [Schedule.moveSteps] <;> omega)]; simp [Schedule.moveWordOffset] <;> rfl
  have placed3 : (if Crypto.BcondCore.bcondC 3#4 e.regs then e.regs._PC + sign_extend (10#19 +++ 0#2) 64
      else e.regs._PC + 4#64) = c.base + offset c (3 + 1) := by
    rw [if_pos taken, target, off4]
  have off3 : offset c 3 = 496#64 := by rw [offset_three c nz, if_neg ne]
  obtain ⟨g, run3, core4, holds3, memory3, _, _, _, frame3, choice3, ev3⟩ :=
    bcondE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget 3 catalogue (by rw [fwd_budget c fwd]; omega) c.page (by rw [off3]; decide)
      3#4 10#19 (by decide) e env3.core nodup low _ placed3 rfl fetch3
  have env4 : EnvM c catalogue entry 4 g := advance0_m c catalogue entry 3 e g env3 core4 choice3
  -- k = 4: MOV x3, x0
  have fetch4 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.OrrMov64.selected 3#5 0#6 0#5) g := by
    exact fetch_index_m c catalogue entry 4 29 g env4 (by decide) (by rw [env4.core.v1.pc, off4]; rfl)
  have placed4 : g.regs._PC + 4#64 = c.base + offset c (4 + 1) := by
    rw [env4.core.v1.pc, off4, show 4 + 1 = 5 + 6 * 0 + 0 by omega, fwd_offset_body c fwd 0 0 (by omega) (by omega)]
    change c.base + 536#64 + 4#64 = c.base + 540#64
    bv_omega
  obtain ⟨x, run4, core5, holds4, memory4, _, _, _, frame4, choice4, ev4⟩ :=
    Route7Steps.mov64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget 4 catalogue (by rw [fwd_budget c fwd]; omega) c.page
      (by rw [off4]; decide) 3#5 0#5 (by decide) (by decide) g env4.core nodup placed4 fetch4
  have env5 : EnvM c catalogue entry 5 x := advance0_m c catalogue entry 4 g x env4 core5 choice4
  obtain ⟨gpr4, sp4⟩ := ValueFacts.mov 3#5 0#5 g x holds4
  change x.regs.gpr = g.regs.gpr.set 3 g.regs.gpr[0] at gpr4
  have gpr : x.regs.gpr = entry.regs.gpr.set 3 c.d := by
    rw [gpr4, ValueFacts.nil_gpr e g holds3, gprE, dest]
  have memory : x.mem = entry.mem := memory4.trans (memory3.trans (memory2.trans (memory1.trans memory0)))
  have bytes : Bytes.CopyPrefix c.srcPA c.dstPA (Aux.memoryView entry) (Aux.memoryView x) c.n 0 := by
    have view : Aux.memoryView x = Aux.memoryView entry := by unfold Aux.memoryView; rw [memory]
    rw [view]
    exact Bytes.copyPrefix_zero c.srcPA c.dstPA (Aux.memoryView entry) c.n
  refine ⟨x, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4], ⟨by omega, by omega,
    by simpa using env5, ?_, ?_, ?_, ?_, ?_, ?_,
    sp4.trans ((ValueFacts.nil_sp e g holds3).trans (sp2.trans (sp1.trans sp0))),
    (((frame0.trans frame1).trans frame2).trans frame3).trans frame4, bytes⟩, ?_, ?_⟩
  · rw [gpr]; simpa using dest
  · rw [gpr]; simpa using source
  · rw [gpr]; simp
  · rw [gpr]; simpa using counter
  · rw [gpr]; simpa using link
  · intro r saved
    have different : 3 ≠ r.val := by omega
    rw [gpr]
    simp [Vector.getElem_set, different]
  · -- coverage (loops)
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5) with hm | hm | hm | hm | hm | hm <;> subst hm
    · exact ⟨entry, rfl, pcOk_of_env_m c catalogue entry _ entry env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_m c catalogue entry _ a env1⟩
    · exact ⟨b, by simp only [Uget.Chain.modelRun, run0, run1], pcOk_of_env_m c catalogue entry _ b env2⟩
    · exact ⟨e, by simp only [Uget.Chain.modelRun, run0, run1, run2], pcOk_of_env_m c catalogue entry _ e env3⟩
    · exact ⟨g, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3], pcOk_of_env_m c catalogue entry _ g env4⟩
    · exact ⟨x, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4], pcOk_of_env_m c catalogue entry _ x env5⟩
  · -- trace (loops CT0): prefix, no data records
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with hj | hj | hj | hj | hj <;> subst hj
    · refine ⟨entry, a, rfl, run0, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ entry env
      · rw [recs_fwd_nil c fwd (0 + 0) (by omega) (by omega)]; exact ⟨ev0, frame0⟩
    · refine ⟨a, b, by simp only [Uget.Chain.modelRun, run0], run1, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ a env1
      · rw [recs_fwd_nil c fwd (0 + 1) (by omega) (by omega)]; exact ⟨ev1, frame1⟩
    · refine ⟨b, e, by simp only [Uget.Chain.modelRun, run0, run1], run2, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ b env2
      · rw [recs_fwd_nil c fwd (0 + 2) (by omega) (by omega)]; exact ⟨ev2, frame2⟩
    · refine ⟨e, g, by simp only [Uget.Chain.modelRun, run0, run1, run2], run3, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ e env3
      · rw [recs_fwd_nil c fwd (0 + 3) (by omega) (by omega)]; exact ⟨ev3, frame3⟩
    · refine ⟨g, x, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3], run4, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ g env4
      · rw [recs_fwd_nil c fwd (0 + 4) (by omega) (by omega)]; exact ⟨ev4, frame4⟩

attribute [local instance 10] Classical.propDecidable in
/-- Backward prefix (s <u d): CBZ, CMP, B.EQ, B.LO not taken, ADD x3, x0, x2; ADD x4, x1, x2 → HeaderB 0 at k = 6. -/
theorem enter_bwd (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (nz : c.n ≠ 0) (ne : c.d ≠ c.s) (ge : ¬ c.d.toNat < c.s.toNat)
    (args : ContractDraft.Args c.d c.s c.returnPC c.n entry) (env : EnvM c catalogue entry 0 entry) :
    ∃ x, Uget.Chain.modelRun real 6 entry = .ok () x ∧ HeaderB c catalogue entry 0 x ∧ Route7Copy.Covered real (PcOkM c) 6 entry ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) 6 0 entry := by
  have bwd := path_backward c nz ne ge
  obtain ⟨dest, source, counter, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[1] = c.s at source
  change entry.regs.gpr[2].toNat = c.n at counter
  change entry.regs.gpr[30] = c.returnPC at link
  obtain ⟨a, run0, env1, memory0, gpr0, sp0, frame0, ev0⟩ := step_cbz real c catalogue nodup entry counter env
  obtain ⟨b, run1, env2, cmp, memory1, gpr1, sp1, frame1, ev1⟩ := step_cmp real c catalogue nodup entry a nz env1
  obtain ⟨e, run2, env3, keep, memory2, gpr2, sp2, frame2, ev2⟩ :=
    step_beq real c catalogue nodup entry a b nz (by rw [gpr0]; exact dest) (by rw [gpr0]; exact source) cmp env2
  have gprE : e.regs.gpr = entry.regs.gpr := gpr2.trans (gpr1.trans gpr0)
  -- k = 3: B.LO 536 (not taken: s <u d)
  have pc3 : e.regs._PC = c.base + 496#64 := by rw [env3.core.v1.pc, offset_three c nz, if_neg ne]
  have fetch3 : FetchObligations c.spec c.config c.rows c.mapping
      (ReleaseProfile.DefaultRuntimeBcondEventTail.W 3#4 10#19) e := by
    exact fetch_index_m c catalogue entry 3 19 e env3 (by decide) (by rw [pc3]; rfl)
  have low : (e.regs._PC + sign_extend (10#19 +++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [pc3]; change (c.base + 496#64 + 40#64).toNat < 2 ^ 55
    have := c.low; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have notTaken : ¬ Crypto.BcondCore.bcondC 3#4 e.regs := by
    rw [bcond_keep 3#4 [] b e keep, cmp_lo a b cmp, gpr0, dest, source]; exact ge
  have off4 : offset c 4 = 500#64 := by
    rw [offset_at c .backward bwd 4 (by simp [Schedule.moveSteps] <;> omega)]; simp [Schedule.moveWordOffset] <;> rfl
  have off5 : offset c 5 = 504#64 := by
    rw [offset_at c .backward bwd 5 (by simp [Schedule.moveSteps] <;> omega)]; simp [Schedule.moveWordOffset] <;> rfl
  have placed3 : (if Crypto.BcondCore.bcondC 3#4 e.regs then e.regs._PC + sign_extend (10#19 +++ 0#2) 64
      else e.regs._PC + 4#64) = c.base + offset c (3 + 1) := by
    rw [if_neg notTaken, pc3, off4]; bv_omega
  have off3 : offset c 3 = 496#64 := by rw [offset_three c nz, if_neg ne]
  obtain ⟨g, run3, core4, holds3, memory3, _, _, _, frame3, choice3, ev3⟩ :=
    bcondE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget 3 catalogue (by rw [bwd_budget c bwd]; omega) c.page (by rw [off3]; decide)
      3#4 10#19 (by decide) e env3.core nodup low _ placed3 rfl fetch3
  have env4 : EnvM c catalogue entry 4 g := advance0_m c catalogue entry 3 e g env3 core4 choice3
  have gprG : g.regs.gpr = entry.regs.gpr := (ValueFacts.nil_gpr e g holds3).trans gprE
  -- k = 4: ADD x3, x0, x2
  have fetch4 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddShift64.selected 3#5 0#5 0#6 2#5) g := by
    exact fetch_index_m c catalogue entry 4 20 g env4 (by decide) (by rw [env4.core.v1.pc, off4]; rfl)
  obtain ⟨h, run4, core5, holds4, memory4, _, _, _, frame4, choice4, ev4⟩ :=
    addShift64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget 4 catalogue (by rw [bwd_budget c bwd]; omega) c.page (by rw [off4]; decide)
      3#5 0#5 2#5 (by decide) (by decide) (by decide) (by decide) g env4.core nodup
      (by rw [env4.core.v1.pc, off4, off5]; bv_omega) fetch4
  have env5 : EnvM c catalogue entry 5 h := advance0_m c catalogue entry 4 g h env4 core5 choice4
  obtain ⟨gpr4, sp4⟩ := addShift_gpr 3#5 0#5 2#5 g h holds4
  change h.regs.gpr = g.regs.gpr.set 3 (g.regs.gpr[0] + g.regs.gpr[2]) at gpr4
  -- k = 5: ADD x4, x1, x2
  have fetch5 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddShift64.selected 4#5 1#5 0#6 2#5) h := by
    exact fetch_index_m c catalogue entry 5 21 h env5 (by decide) (by rw [env5.core.v1.pc, off5]; rfl)
  obtain ⟨x, run5, core6, holds5, memory5, _, _, _, frame5, choice5, ev5⟩ :=
    addShift64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget 5 catalogue (by rw [bwd_budget c bwd]; omega) c.page (by rw [off5]; decide)
      4#5 1#5 2#5 (by decide) (by decide) (by decide) (by decide) h env5.core nodup
      (by rw [env5.core.v1.pc, off5, show 5 + 1 = 6 + 6 * 0 + 0 by omega, bwd_offset_body c bwd 0 0 (by omega) (by omega)]
          change c.base + 504#64 + 4#64 = c.base + 508#64; bv_omega) fetch5
  have env6 : EnvM c catalogue entry 6 x := advance0_m c catalogue entry 5 h x env5 core6 choice5
  obtain ⟨gpr5, sp5⟩ := addShift_gpr 4#5 1#5 2#5 h x holds5
  change x.regs.gpr = h.regs.gpr.set 4 (h.regs.gpr[1] + h.regs.gpr[2]) at gpr5
  have countVal : entry.regs.gpr[2] = BitVec.ofNat 64 c.n := by
    apply BitVec.eq_of_toNat_eq; rw [counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := entry.regs.gpr[2].isLt; omega
  have gpr : x.regs.gpr = (entry.regs.gpr.set 3 (c.d + BitVec.ofNat 64 c.n)).set 4 (c.s + BitVec.ofNat 64 c.n) := by
    rw [gpr5, gpr4, gprG]
    simp [dest, source, countVal]
  have memory : x.mem = entry.mem :=
    memory5.trans (memory4.trans (memory3.trans (memory2.trans (memory1.trans memory0))))
  have bytes : Bytes.CopyPrefix c.srcR c.dstR (Aux.memoryView entry) (Aux.memoryView x) c.n 0 := by
    have view : Aux.memoryView x = Aux.memoryView entry := by unfold Aux.memoryView; rw [memory]
    rw [view]
    exact Bytes.copyPrefix_zero c.srcR c.dstR (Aux.memoryView entry) c.n
  refine ⟨x, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4, run5], ⟨by omega, by omega,
    by simpa using env6, ?_, ?_, ?_, ?_, ?_, ?_,
    sp5.trans (sp4.trans ((ValueFacts.nil_sp e g holds3).trans (sp2.trans (sp1.trans sp0)))),
    ((((frame0.trans frame1).trans frame2).trans frame3).trans frame4).trans frame5, bytes⟩, ?_, ?_⟩
  · rw [gpr]; simpa using dest
  · rw [gpr]; simp
  · rw [gpr]; simp
  · rw [gpr]; simpa using counter
  · rw [gpr]; simpa using link
  · intro r saved
    have n3 : 3 ≠ r.val := by omega
    have n4 : 4 ≠ r.val := by omega
    rw [gpr]
    simp [Vector.getElem_set, n3, n4]
  · -- coverage (loops)
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6) with hm | hm | hm | hm | hm | hm | hm <;> subst hm
    · exact ⟨entry, rfl, pcOk_of_env_m c catalogue entry _ entry env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_m c catalogue entry _ a env1⟩
    · exact ⟨b, by simp only [Uget.Chain.modelRun, run0, run1], pcOk_of_env_m c catalogue entry _ b env2⟩
    · exact ⟨e, by simp only [Uget.Chain.modelRun, run0, run1, run2], pcOk_of_env_m c catalogue entry _ e env3⟩
    · exact ⟨g, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3], pcOk_of_env_m c catalogue entry _ g env4⟩
    · exact ⟨h, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4], pcOk_of_env_m c catalogue entry _ h env5⟩
    · exact ⟨x, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4, run5], pcOk_of_env_m c catalogue entry _ x env6⟩
  · -- trace (loops CT0): prefix, no data records
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with hj | hj | hj | hj | hj | hj <;> subst hj
    · refine ⟨entry, a, rfl, run0, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ entry env
      · rw [recs_bwd_nil c bwd (0 + 0) (by omega) (by omega)]; exact ⟨ev0, frame0⟩
    · refine ⟨a, b, by simp only [Uget.Chain.modelRun, run0], run1, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ a env1
      · rw [recs_bwd_nil c bwd (0 + 1) (by omega) (by omega)]; exact ⟨ev1, frame1⟩
    · refine ⟨b, e, by simp only [Uget.Chain.modelRun, run0, run1], run2, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ b env2
      · rw [recs_bwd_nil c bwd (0 + 2) (by omega) (by omega)]; exact ⟨ev2, frame2⟩
    · refine ⟨e, g, by simp only [Uget.Chain.modelRun, run0, run1, run2], run3, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ e env3
      · rw [recs_bwd_nil c bwd (0 + 3) (by omega) (by omega)]; exact ⟨ev3, frame3⟩
    · refine ⟨g, h, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3], run4, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ g env4
      · rw [recs_bwd_nil c bwd (0 + 4) (by omega) (by omega)]; exact ⟨ev4, frame4⟩
    · refine ⟨h, x, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4], run5, ?_, ?_⟩
      · rw [Nat.zero_add]; exact pcAt_of_env_m c catalogue entry _ h env5
      · rw [recs_bwd_nil c bwd (0 + 5) (by omega) (by omega)]; exact ⟨ev5, frame5⟩

/-! ## Loop inductions -/

theorem header_source_f (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry x : NativeState) (i : Nat)
    (room : i < c.n) (present : ContractDraft.SourcePresent c.mapping c.s c.n entry) (header : HeaderF c catalogue entry i x) :
    ∃ byte, Aux.memoryView x (c.srcPA i) = some byte := by
  obtain ⟨pa, mapped, _, _⟩ := source_mapped c i room
  obtain ⟨byte, initial⟩ := present i room
  have physical : c.srcPA i = pa.toNat := by simp only [Context.srcPA, mapped, Option.getD_some]
  simp only [readByte, mapped, Option.bind_some] at initial
  refine ⟨byte, ?_⟩
  rw [header.bytes.unread i (Nat.le_refl _) room]
  simpa only [Aux.memoryView, physical] using initial

theorem header_source_b (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry x : NativeState) (t : Nat)
    (room : t < c.n) (present : ContractDraft.SourcePresent c.mapping c.s c.n entry) (header : HeaderB c catalogue entry t x) :
    ∃ byte, Aux.memoryView x (c.srcR t) = some byte := by
  have ir : c.n - 1 - t < c.n := by omega
  obtain ⟨pa, mapped, _, _⟩ := source_mapped c (c.n - 1 - t) ir
  obtain ⟨byte, initial⟩ := present (c.n - 1 - t) ir
  have physical : c.srcPA (c.n - 1 - t) = pa.toNat := by simp only [Context.srcPA, mapped, Option.getD_some]
  simp only [readByte, mapped, Option.bind_some] at initial
  refine ⟨byte, ?_⟩
  rw [header.bytes.unread t (Nat.le_refl _) room]
  simpa only [Context.srcR, Aux.memoryView, physical] using initial

theorem finish_fwd (real : Type) [Sail.SailReal real] (c : Context) (fwd : c.path = .forward)
    (lt : c.d.toNat < c.s.toNat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (present : ContractDraft.SourcePresent c.mapping c.s c.n entry) (i : Nat) (x : NativeState)
    (header : HeaderF c catalogue entry i x) :
    ∃ fin, Uget.Chain.modelRun real (6 * (c.n - i) + 1) x = .ok () fin ∧
      MovePost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Route7Copy.Covered real (PcOkM c) (6 * (c.n - i) + 1) x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) (6 * (c.n - i) + 1) (5 + 6 * i) x := by
  suffices all : ∀ remaining i x, c.n - i = remaining → HeaderF c catalogue entry i x →
      ∃ fin, Uget.Chain.modelRun real (6 * remaining + 1) x = .ok () fin ∧
        MovePost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Route7Copy.Covered real (PcOkM c) (6 * remaining + 1) x ∧
        Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) (6 * remaining + 1) (5 + 6 * i) x by
    exact all (c.n - i) i x rfl header
  intro remaining
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    intro i x rank header
    by_cases zero : remaining = 0
    · have last : i = c.n := by have bound := header.bound; omega
      subst i
      obtain ⟨fin, run, _, _, post, cov, tr1⟩ := fwd_exit real c fwd catalogue nodup entry x header
      subst zero
      exact ⟨fin, run, post, cov, tr1⟩
    · have room : i < c.n := by have bound := header.bound; omega
      obtain ⟨byte, value⟩ := header_source_f c catalogue entry x i room present header
      obtain ⟨next, run, _, nextHeader, bodyCov, bodyTr⟩ := fwd_body real c fwd lt catalogue nodup entry x i room byte header value
      obtain ⟨fin, rest, post, restCov, restTr⟩ := ih (c.n - (i + 1)) (by omega) (i + 1) next rfl nextHeader
      refine ⟨fin, ?_, post, ?_, ?_⟩
      · rw [show 6 * remaining + 1 = 6 + (6 * (c.n - (i + 1)) + 1) by omega]
        exact Aux.modelRun_append real 6 (6 * (c.n - (i + 1)) + 1) x next fin run rest
      · rw [show 6 * remaining + 1 = 6 + (6 * (c.n - (i + 1)) + 1) by omega]
        exact Route7Copy.covered_append real (PcOkM c) 6 (6 * (c.n - (i + 1)) + 1) x next run bodyCov restCov
      · rw [show 6 * remaining + 1 = 6 + (6 * (c.n - (i + 1)) + 1) by omega]
        exact Route7Trace.traced_append real c.spec c.mapping (recsOfM c) (pcOfM c) 6 (6 * (c.n - (i + 1)) + 1) (5 + 6 * i) x next run bodyTr
          (by rw [show 5 + 6 * i + 6 = 5 + 6 * (i + 1) by omega]; exact restTr)

theorem finish_bwd (real : Type) [Sail.SailReal real] (c : Context) (bwd : c.path = .backward)
    (gt : c.s.toNat < c.d.toNat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (present : ContractDraft.SourcePresent c.mapping c.s c.n entry) (t : Nat) (x : NativeState)
    (header : HeaderB c catalogue entry t x) :
    ∃ fin, Uget.Chain.modelRun real (6 * (c.n - t) + 1) x = .ok () fin ∧
      MovePost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Route7Copy.Covered real (PcOkM c) (6 * (c.n - t) + 1) x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) (6 * (c.n - t) + 1) (6 + 6 * t) x := by
  suffices all : ∀ remaining t x, c.n - t = remaining → HeaderB c catalogue entry t x →
      ∃ fin, Uget.Chain.modelRun real (6 * remaining + 1) x = .ok () fin ∧
        MovePost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Route7Copy.Covered real (PcOkM c) (6 * remaining + 1) x ∧
        Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) (6 * remaining + 1) (6 + 6 * t) x by
    exact all (c.n - t) t x rfl header
  intro remaining
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    intro t x rank header
    by_cases zero : remaining = 0
    · have last : t = c.n := by have bound := header.bound; omega
      subst t
      obtain ⟨fin, run, _, _, post, cov, tr1⟩ := bwd_exit real c bwd catalogue nodup entry x header
      subst zero
      exact ⟨fin, run, post, cov, tr1⟩
    · have room : t < c.n := by have bound := header.bound; omega
      obtain ⟨byte, value⟩ := header_source_b c catalogue entry x t room present header
      obtain ⟨next, run, _, nextHeader, bodyCov, bodyTr⟩ := bwd_body real c bwd gt catalogue nodup entry x t room byte header value
      obtain ⟨fin, rest, post, restCov, restTr⟩ := ih (c.n - (t + 1)) (by omega) (t + 1) next rfl nextHeader
      refine ⟨fin, ?_, post, ?_, ?_⟩
      · rw [show 6 * remaining + 1 = 6 + (6 * (c.n - (t + 1)) + 1) by omega]
        exact Aux.modelRun_append real 6 (6 * (c.n - (t + 1)) + 1) x next fin run rest
      · rw [show 6 * remaining + 1 = 6 + (6 * (c.n - (t + 1)) + 1) by omega]
        exact Route7Copy.covered_append real (PcOkM c) 6 (6 * (c.n - (t + 1)) + 1) x next run bodyCov restCov
      · rw [show 6 * remaining + 1 = 6 + (6 * (c.n - (t + 1)) + 1) by omega]
        exact Route7Trace.traced_append real c.spec c.mapping (recsOfM c) (pcOfM c) 6 (6 * (c.n - (t + 1)) + 1) (6 + 6 * t) x next run bodyTr
          (by rw [show 6 + 6 * t + 6 = 6 + 6 * (t + 1) by omega]; exact restTr)

/-! ## Complete memmove -/

/-- **Complete memmove over the MTE2-general Runtime InvG** (route 7 breadth): from EnvM at the actual entry
(CurrentInv + tag-status rows, e.g. from Route7Entry.invG_at_entry), the exact schedule length
moveSteps (movePath d s n) n runs successfully to MovePost: x0 = d, RET to returnPC, every destination byte equal to
the ENTRY source byte (overlap-correct; no disjointness premise), everything outside the destination unchanged. -/
theorem run_m (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (args : ContractDraft.Args c.d c.s c.returnPC c.n entry)
    (present : ContractDraft.SourcePresent c.mapping c.s c.n entry) (env : EnvM c catalogue entry 0 entry) :
    ∃ fin, Uget.Chain.modelRun real c.budget entry = .ok () fin ∧
      MovePost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Route7Copy.Covered real (PcOkM c) c.budget entry ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) c.budget 0 entry := by
  by_cases zero : c.n = 0
  · exact empty_m real c catalogue nodup entry zero args env
  by_cases same : c.d = c.s
  · exact same_m real c catalogue nodup entry zero same args env
  by_cases lt : c.d.toNat < c.s.toNat
  · have fwd := path_forward c zero same lt
    obtain ⟨header, firstRun, init, enterCov, enterTr⟩ := enter_fwd real c catalogue nodup entry zero same lt args env
    obtain ⟨fin, restRun, post, restCov, restTr⟩ := finish_fwd real c fwd lt catalogue nodup entry present 0 header init
    refine ⟨fin, ?_, post, ?_, ?_⟩
    · rw [fwd_budget c fwd, show 6 * c.n + 6 = 5 + (6 * (c.n - 0) + 1) by omega]
      exact Aux.modelRun_append real 5 (6 * (c.n - 0) + 1) entry header fin firstRun restRun
    · rw [fwd_budget c fwd, show 6 * c.n + 6 = 5 + (6 * (c.n - 0) + 1) by omega]
      exact Route7Copy.covered_append real (PcOkM c) 5 (6 * (c.n - 0) + 1) entry header firstRun enterCov restCov
    · rw [fwd_budget c fwd, show 6 * c.n + 6 = 5 + (6 * (c.n - 0) + 1) by omega]
      exact Route7Trace.traced_append real c.spec c.mapping (recsOfM c) (pcOfM c) 5 (6 * (c.n - 0) + 1) 0 entry header firstRun enterTr
        (by simpa only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] using restTr)
  · have bwd := path_backward c zero same lt
    have gt : c.s.toNat < c.d.toNat := by
      have : c.d.toNat ≠ c.s.toNat := fun h => same (BitVec.eq_of_toNat_eq h)
      omega
    obtain ⟨header, firstRun, init, enterCov, enterTr⟩ := enter_bwd real c catalogue nodup entry zero same lt args env
    obtain ⟨fin, restRun, post, restCov, restTr⟩ := finish_bwd real c bwd gt catalogue nodup entry present 0 header init
    refine ⟨fin, ?_, post, ?_, ?_⟩
    · rw [bwd_budget c bwd, show 6 * c.n + 7 = 6 + (6 * (c.n - 0) + 1) by omega]
      exact Aux.modelRun_append real 6 (6 * (c.n - 0) + 1) entry header fin firstRun restRun
    · rw [bwd_budget c bwd, show 6 * c.n + 7 = 6 + (6 * (c.n - 0) + 1) by omega]
      exact Route7Copy.covered_append real (PcOkM c) 6 (6 * (c.n - 0) + 1) entry header firstRun enterCov restCov
    · rw [bwd_budget c bwd, show 6 * c.n + 7 = 6 + (6 * (c.n - 0) + 1) by omega]
      exact Route7Trace.traced_append real c.spec c.mapping (recsOfM c) (pcOfM c) 6 (6 * (c.n - 0) + 1) 0 entry header firstRun enterTr
        (by simpa only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] using restTr)

end Route7Move

#print axioms Route7Move.step_cbz
#print axioms Route7Move.step_cmp
#print axioms Route7Move.step_beq
#print axioms Route7Move.empty_m
#print axioms Route7Move.same_m
#print axioms Route7Move.enter_fwd
#print axioms Route7Move.enter_bwd
#print axioms Route7Move.finish_fwd
#print axioms Route7Move.finish_bwd
#print axioms Route7Move.run_m
