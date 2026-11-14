-- Route 7 breadth: memset environment over Runtime InvG (CurrentInv + MTE tag-status rows/trace),
-- ported from loops SetContext the way ported CopyContext to Route7Copy.Context.
import ArmCertLoop.SetContext
import Route7Copy.Context
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

namespace Route7Set
open ArmCertLoop ArmCertLoop.SetNative ArmCertLoop.ContractDraft

/-- Is step k the STRB of iteration (k-2)/4 (memset has one memory step per 4-step iteration)? -/
def setStep (n k : Nat) : Bool := decide (2 ≤ k ∧ (k - 2) % 4 = 0 ∧ (k - 2) / 4 < n)

/-- STRB steps strictly before step k (each draws at most one MTE tag status). -/
def setPast (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => setPast n k + (if setStep n k then 1 else 0)

theorem setPast_succ (n k : Nat) : setPast n (k + 1) = setPast n k + (if setStep n k then 1 else 0) := rfl

/-- The memset environment: Runtime InvG over loops SetNative.Context, tag-status capacity n. -/
abbrev EnvS (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat) (x : NativeState) : Prop :=
  ReleaseProfile.DefaultRuntime.InvG c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
    (offset c) (Schedule.setSteps c.n) (fun _ _ => True) catalogue entry c.n (setPast c.n) k x

theorem pc_body_s (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (i j : Nat) (room : i < c.n) (slot : j < 4) (x : NativeState) (env : EnvS c catalogue entry (2 + 4 * i + j) x) :
    x.regs._PC = MemReloc.imageAddress c.base (464 + 4 * j) := by
  rw [env.core.v1.pc, offset_body c i j room slot]
  rfl

def fetch_index_s (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k index : Nat)
    (x : NativeState) (env : EnvS c catalogue entry k x)
    (room : index < Generated.imageWords.length)
    (pc : x.regs._PC = MemReloc.imageAddress c.base (Generated.imageStart + 4 * index)) :
    FetchObligations c.spec c.config c.rows c.mapping (Generated.imageWords.getD index 0) x :=
  Route7Copy.fetch_word_cur c.spec c.config c.rows c.mapping c.spans
    (rowsFootprint c.spec.imageRows).byte codeScope c.base Generated.imageStart Generated.imageWords
    (offset c) (Schedule.setSteps c.n) k catalogue index room x env.core pc
    (fun byte bounded => by unfold codeScope; have := room; simp only [Generated.imageWords_length, Generated.imageStart] at *; omega)
    (c.code index room).1 (c.code index room).2 c.separated

theorem body_next_placed_s (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (i j : Nat) (room : i < c.n) (slot : j < 3)
    (x : NativeState) (env : EnvS c catalogue entry (2 + 4 * i + j) x) :
    x.regs._PC + 4#64 = c.base + offset c (2 + 4 * i + j + 1) := by
  rw [pc_body_s c catalogue entry i j room (by omega) x env]
  have index : 2 + 4 * i + j + 1 = 2 + 4 * i + (j + 1) := by omega
  rw [index, offset_body c i (j + 1) room (by omega)]
  unfold MemReloc.imageAddress
  have word : 464 + 4 * (j + 1) = (464 + 4 * j) + 4 := by omega
  rw [word]
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

theorem setStep_body (n i j : Nat) (hi : i < n) (hj : j < 4) : setStep n (2 + 4 * i + j) = decide (j = 0) := by
  unfold setStep
  by_cases h : j = 0
  · subst h; simp; omega
  · have : (2 + 4 * i + j - 2) % 4 ≠ 0 := by omega
    simp [h, this]

theorem setPast_body (n i : Nat) (hi : i ≤ n) : setPast n (2 + 4 * i) = i := by
  induction i with
  | zero => simp [setPast, setStep]
  | succ m ih =>
    have e : 2 + 4 * (m + 1) = 2 + 4 * m + 3 + 1 := by omega
    rw [e, setPast_succ, show 2 + 4 * m + 3 = 2 + 4 * m + 2 + 1 by omega, setPast_succ,
      show 2 + 4 * m + 2 = 2 + 4 * m + 1 + 1 by omega, setPast_succ, show 2 + 4 * m + 1 = 2 + 4 * m + 0 + 1 by omega,
      setPast_succ, show 2 + 4 * m + 0 = 2 + 4 * m by omega, ih (by omega)]
    have h0 : setStep n (2 + 4 * m) = true := by simpa using setStep_body n m 0 (by omega) (by omega)
    simp [h0, setStep_body n m 1 (by omega) (by omega),
      setStep_body n m 2 (by omega) (by omega), setStep_body n m 3 (by omega) (by omega)]

theorem setStep_store (n i : Nat) (hi : i < n) : setStep n (2 + 4 * i) = true := by
  simpa using setStep_body n i 0 hi (by decide)

theorem setStep_other (n i j : Nat) (hi : i < n) (hj0 : 0 < j) (hj : j < 4) : setStep n (2 + 4 * i + j) = false := by
  rw [setStep_body n i j hi hj]; simp; omega

/-- A zero-draw step advances EnvS at a non-store index of an iteration. -/
theorem advance0_s (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (i j : Nat)
    (room : i < c.n) (hj0 : 0 < j) (hj : j < 4) (x fin : NativeState)
    (env : EnvS c catalogue entry (2 + 4 * i + j) x)
    (core : ReleaseProfile.DefaultCurrent.CurrentInv c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
      (offset c) (Schedule.setSteps c.n) (2 + 4 * i + j + 1) catalogue fin)
    (choice : NativeMteTagCheck.ChoiceDelta x fin 0) : EnvS c catalogue entry (2 + 4 * i + j + 1) fin :=
  ReleaseProfile.DefaultRuntime.InvG.advance env core True.intro ⟨0, choice, Nat.le_refl 0⟩
    (by rw [setPast_succ, setStep_other c.n i j room hj0 hj]; simp)

end Route7Set

#print axioms Route7Set.setPast_succ
#print axioms Route7Set.pc_body_s
#print axioms Route7Set.fetch_index_s
#print axioms Route7Set.body_next_placed_s
#print axioms Route7Set.setPast_body
