-- Additive route4 value language: legacy instructions and byte-span stores from a value expression.
-- Existing Core, Op, Def, Sym, and all frozen release modules are unchanged.
import ArmCertValue.PhysicalSSA
import ArmCertValue.PhysicalGlue
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.F
open HeapV2StepCerts.RegBind (Reg St regVal)
open ArmCertValue.Physical (BytePA)

inductive Step where
  | legacy (step : StepV)
  | store (width : Nat) (source : VUpd) (region : Region) (byte : Nat)

/-- The byte positions written by a single span store. -/
def WritesAt (region : Region) (byte width : Nat) (q : Region) (j : Nat) : Prop :=
  q = region ∧ byte ≤ j ∧ j < byte + width

instance (r q : Region) (j k n : Nat) : Decidable (WritesAt r j n q k) := inferInstanceAs (Decidable (q = r ∧ j ≤ k ∧ k < j + n))

/-- Memory payload and frame; actual Sail routes must establish both. -/
def StoreHolds (bytePA : BytePA) (regions : List Region) (width : Nat) (source : VUpd)
    (region : Region) (byte : Nat) (x y : St) : Prop :=
  (∀ t, t < width → Physical.regionByte bytePA y region (byte + t) =
    some (((source.eval x) >>> (8 * t)).setWidth 8)) ∧
  (∀ q ∈ regions, ∀ j, j < 8 * q.words → ¬ WritesAt region byte width q j →
    Physical.regionByte bytePA y q j = Physical.regionByte bytePA x q j)

def Holds (bytePA : BytePA) (regions : List Region) : Step → St → St → Prop
  | .legacy s, x, y => VHolds s.us s.fl x y ∧ Physical.MemVHolds bytePA regions s.mem x y
  | .store n u r j, x, y => VHolds [] none x y ∧ StoreHolds bytePA regions n u r j x y

/-- A stored value is appended once; each written byte selects its byte in that SSA value. -/
def storeMap (σ : Sym) (id : Nat) (regions : List Region) (r : Region) (j n : Nat) : Sym where
  regs := σ.regs
  nzcv := σ.nzcv
  memB := fun q k =>
    if q ∈ regions ∧ k < 8 * q.words then
      if WritesAt r j n q k then some (id, k - j) else σ.memB q k
    else none

def compile (σ : Sym) (n : Nat) (regions : List Region) : Step → Option (List Def × Sym)
  | .legacy s => ArmCertValue.compile σ n regions s
  | .store width u r j =>
    if 0 < width ∧ width ≤ 8 ∧ r ∈ regions ∧ j + width ≤ 8 * r.words then
      (defOf σ u).map fun d => ([d], storeMap σ n regions r j width)
    else none

@[simp] theorem compile_legacy (σ : Sym) (n : Nat) (rs : List Region) (s : StepV) :
    compile σ n rs (.legacy s) = ArmCertValue.compile σ n rs s := rfl

theorem compile_store (σ : Sym) (n : Nat) (rs : List Region) (width : Nat) (u : VUpd) (r : Region) (j : Nat)
    (valid : 0 < width ∧ width ≤ 8 ∧ r ∈ rs ∧ j + width ≤ 8 * r.words)
    (d : Def) (hd : defOf σ u = some d) :
    compile σ n rs (.store width u r j) = some ([d], storeMap σ n rs r j width) := by
  simp only [compile, if_pos valid, hd, Option.map_some]

/-- Prototype for STR XZR: an eight-byte literal store has no fake register source. -/
theorem compile_zero8 (σ : Sym) (n : Nat) (rs : List Region) (r : Region) (j : Nat)
    (hr : r ∈ rs) (fits : j + 8 ≤ 8 * r.words) :
    compile σ n rs (.store 8 ⟨.const 0#64, []⟩ r j) =
      some ([⟨.const 0#64, []⟩], storeMap σ n rs r j 8) := by
  apply compile_store _ _ _ _ _ _ _ ⟨by decide, by decide, hr, fits⟩
  rfl

/-- The compiler's stored-byte case or an unchanged, supported source byte. -/
theorem storeMap_spec (σ : Sym) (id : Nat) (rs : List Region) (r : Region) (j n : Nat)
    {q : Region} {k i b : Nat} (h : (storeMap σ id rs r j n).memB q k = some (i,b)) :
    q ∈ rs ∧ k < 8 * q.words ∧
      ((WritesAt r j n q k ∧ i = id ∧ b = k-j) ∨ (¬ WritesAt r j n q k ∧ σ.memB q k = some (i,b))) := by
  simp only [storeMap] at h
  split at h
  · next support =>
    refine ⟨support.1, support.2, ?_⟩
    split at h
    · next written =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨written, h.1.symm, h.2.symm⟩
    · next outside => exact Or.inr ⟨outside,h⟩
  · cases h

/-- One compiled step preserves the physical-byte SSA relation. This is a value-layer theorem, not a Sail interpreter. -/
theorem step_agrees {bytePA : BytePA} {vals : List (BitVec 64)} {σ τ : Sym} {x y : St}
    {regions : List Region} {s : Step} {ds : List Def}
    (hA : Physical.Agrees bytePA vals σ x) (hB : σ.Bounded vals.length)
    (hh : Holds bytePA regions s x y) (hc : compile σ vals.length regions s = some (ds,τ)) :
    Physical.Agrees bytePA (extend vals ds) τ y ∧ τ.Bounded (extend vals ds).length := by
  cases s with
  | legacy s => exact Physical.step_agrees hA hB hh.1 hh.2 hc
  | store width u r j =>
    simp only [compile] at hc
    split at hc
    · next valid =>
      obtain ⟨d,hd,he⟩ := Option.map_eq_some_iff.1 hc
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      obtain ⟨hv,hm⟩ := hh
      have vd := (Physical.defOf_sound hA hB u d hd).1
      have ext : extend vals [d] = vals ++ [d.eval vals] := rfl
      have len : (extend vals [d]).length = vals.length + 1 := by simp only [ext, List.length_append, List.length_singleton]
      have old : ∀ i, i < vals.length → (extend vals [d]).getD i 0 = vals.getD i 0 := by
        intro i hi; rw [ext]; exact getD_left _ _ _ hi
      have fresh : (extend vals [d]).getD vals.length 0 = u.eval x := by
        calc
          _ = d.eval vals := by simpa only [ext, Nat.add_zero, List.getD_cons_zero] using (getD_right vals [d.eval vals] 0)
          _ = _ := vd
      refine ⟨⟨?_,?_,?_⟩,⟨?_,?_,?_⟩⟩
      · intro q i h
        have reg := hv.1 q
        change regVal y q = regVal x q at reg
        rw [reg, hA.1 q i h, old i (hB.1 q i h)]
      · intro a b c d h
        obtain ⟨ha,hb,hc,hd⟩ := hA.2.1 a b c d h
        obtain ⟨ba,bb,bc,bd⟩ := hB.2.1 a b c d h
        refine ⟨?_,?_,?_,?_⟩
        · rw [old a ba, ←ha]; exact hv.2 0
        · rw [old b bb, ←hb]; exact hv.2 1
        · rw [old c bc, ←hc]; exact hv.2 2
        · rw [old d bd, ←hd]; exact hv.2 3
      · intro q k i b h
        obtain ⟨member,bound, written | outside⟩ := storeMap_spec σ vals.length regions r j width h
        · obtain ⟨⟨rfl,lo,hi⟩,rfl,rfl⟩ := written
          have hb := hm.1 (k-j) (by omega)
          rw [show j+(k-j)=k by omega] at hb
          rw [fresh]; exact hb
        · rw [hm.2 q member k bound outside.1, hA.2.2 q k i b outside.2, old i (hB.2.2 q k i b outside.2)]
      · intro q i h
        have b := hB.1 q i h
        rw [len]; omega
      · intro a b c d h
        obtain ⟨ha,hb,hc,hd⟩ := hB.2.1 a b c d h
        rw [len]; exact ⟨by omega,by omega,by omega,by omega⟩
      · intro q k i b h
        obtain ⟨_,_, written | outside⟩ := storeMap_spec σ vals.length regions r j width h
        · rw [written.2.1,len]; omega
        · have bound := hB.2.2 q k i b outside.2
          rw [len]; omega
    · cases hc

/-- Same per-step actual Sail success interface as the legacy pipeline, for the additive language. -/
def StepFact (real : Type) [Sail.SailReal real] (Inv : Nat → ArmBridge.Draft.NativeState → Prop)
    (bytePA : BytePA) (regions : List Region) (plan : List Step) (k : Nat) (hk : k < plan.length) : Prop :=
  ∀ x, Inv k x → ∃ fin, ArmBridge.Boundary.modelStep real x = .ok () fin ∧ Holds bytePA regions plan[k] x fin

def compileRun (regions : List Region) : Sym → Nat → List Step → Option (List Def × Sym)
  | σ, _, [] => some ([], σ)
  | σ, n, st :: rest => match compile σ n regions st with
    | some (ds, σ1) => match compileRun regions σ1 (n + ds.length) rest with
      | some (ds', σf) => some (ds ++ ds', σf)
      | none => none
    | none => none


def PlanHolds (bytePA : BytePA) (regions : List Region)
    (run : Nat → St) (k : Nat) (plan : List Step) : Prop :=
  ∀ j (h : j < plan.length), Holds bytePA regions plan[j] (run (k + j)) (run (k + j + 1))

theorem run_agrees (bytePA : BytePA) (regions : List Region)
    (run : Nat → St) :
    ∀ (plan : List Step) (k : Nat) (vals : List (BitVec 64)) (σ σf : Sym) (ds : List Def),
      Physical.Agrees bytePA vals σ (run k) → σ.Bounded vals.length →
      PlanHolds bytePA regions run k plan →
      compileRun regions σ vals.length plan = some (ds, σf) →
      Physical.Agrees bytePA (extend vals ds) σf (run (k + plan.length)) ∧
        σf.Bounded (extend vals ds).length := by
  intro plan
  induction plan with
  | nil =>
    intro k vals σ σf ds hA hB _ hc
    simp only [compileRun, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simpa [extend] using And.intro hA hB
  | cons st rest ih =>
    intro k vals σ σf ds hA hB hp hc
    simp only [compileRun] at hc
    split at hc
    · next ds1 σ1 h1 =>
      split at hc
      · next ds2 σ2 h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have h0 := hp 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at h0
        obtain ⟨hA1, hB1⟩ := step_agrees hA hB h0 h1
        have hlen : (extend vals ds1).length = vals.length + ds1.length := extend_length vals ds1
        have hp' : PlanHolds bytePA regions run (k + 1) rest := by
          intro j hj
          have := hp (j + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at this
          rw [show k + 1 + j = k + (j + 1) by omega]
          exact this
        have := ih (k + 1) (extend vals ds1) σ1 σ2 ds2 hA1 hB1 hp' (by rw [hlen]; exact h2)
        rw [extend_append, List.length_cons, show k + (rest.length + 1) = k + 1 + rest.length by omega]
        simpa using this
      · simp at hc
    · simp at hc



open CertiFFI.Prog.Generic.ModelRunView

theorem planHolds_of_steps (real : Type) [Sail.SailReal real]
    (Inv : Nat → ArmBridge.Draft.NativeState → Prop)
    (bytePA : BytePA) (regions : List Region) (plan : List Step)
    (e : ArmBridge.Draft.NativeState)
    (hinv : ∀ k, k < plan.length → Inv k (stateAt real e k))
    (hstep : ∀ k (h : k < plan.length), StepFact real Inv bytePA regions plan k h) :
    PlanHolds bytePA regions (stateAt real e) 0 plan := by
  intro j hj
  obtain ⟨fin, run, hh⟩ := hstep j hj _ (hinv j hj)
  have hs := Physical.stateAt_succ_of' run
  simp only [Nat.zero_add]
  rw [hs]
  exact hh

#print axioms run_agrees
#print axioms planHolds_of_steps

#print axioms compile_zero8
#print axioms step_agrees
end ArmCertValue.F
