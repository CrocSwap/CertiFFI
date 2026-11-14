import MemM1.ConsumerV3
import MemM1.WalkKE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
namespace MemM1.ConsumerV3K
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.Witness MemM1.WalkFactV MemM1.ConsumerV2 MemM1.ConsumerD MemM1.ConsumerV3
open ArmCert.Eval.M1a.WEv (WalkFactE)
open MemM1.WalkKE (walkK tr_dataE)

/-! E17 v3 for `kmap` with the run's walk `walkK s.regs s.mem`, from eval's `WalkFactE` per page.
The data branch is `WalkKE.tr_dataE`; the IFETCH branch still takes `EvIF` (to be closed by
`tr_ifE`). -/

/-- The data event clause from `tr_dataE` (TranslateAddress is deterministic). -/
theorem evData_K (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFactE s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf)) :
    EvData (walkK s.regs s.mem) s P := by
  intro u hu hum va p acc al sz ad t hva hp hc hA hTA
  rcases hP va p hva hp with ⟨hWE, hD⟩
  simp only [hc, Bool.false_eq_true, ↓reduceIte] at hD
  rcases tr_dataE s hR hC va hva p.leaf hWE hD acc hA al sz u hu hum with
    ⟨ad', t', h, _, _, _, _, _, _, _, _, _, ti, W, hev, hW⟩
  rw [hTA] at h
  injection h with had ht
  subst had ht
  exact ⟨ti, W, hev, hW⟩

/-- **E17 v3 for `kmap P` with `walk := walkK s.regs s.mem`** (IFETCH clause `EvIF` assumed). -/
theorem agreesV3_kmapK (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFactE s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf))
    (hIF : EvIF (walkK s.regs s.mem) s P) :
    AgreesV3 (kmap P) (walkK s.regs s.mem) s :=
  agreesV3_kmap s hR hC P _
    (fun va p hva hp => ⟨(hP va p hva hp).1.walkFact, (hP va p hva hp).2⟩)
    (evData_K s hR hC P hP) hIF

/-- **E17 v3 for a data-only `kmap P`** (no code pages; `EvIF` is vacuous). -/
theorem agreesV3_kmapK_data (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFactE s va p.leaf ∧ LeafBitsD p.leaf)
    (hdata : ∀ n p, P n = some p → p.code = false) :
    AgreesV3 (kmap P) (walkK s.regs s.mem) s :=
  agreesV3_kmapK s hR hC P
    (fun va p hva hp => by
      rw [hdata _ p hp]
      exact ⟨(hP va p hva hp).1, (hP va p hva hp).2⟩)
    (evIF_of_data _ s P hdata)

/-- A data access inside one mapped data page below 2^48 is permitted by `kmap P`. -/
theorem kmap_permitted (P : BitVec 64 → Option Page) (a : BitVec 64) (p : Page) (n : Nat)
    (ha : a.toNat < 2^48) (hp : P (a >>> 12) = some p) (hdata : p.code = false) (hn : 0 < n)
    (hin : a.toNat % 4096 + n ≤ 4096) :
    ∀ acc, Acc0 acc → (kmap P).permitted a acc true (n : Int) := by
  intro acc hA
  refine ⟨ha, by omega, by omega, p, hp, ?_⟩
  rw [hdata]
  exact hA

/-- An instruction fetch inside one mapped code page below 2^48 is permitted by `kmap P`. -/
theorem kmap_permitted_code (P : BitVec 64 → Option Page) (a : BitVec 64) (p : Page) (n : Nat)
    (ha : a.toNat < 2^48) (hp : P (a >>> 12) = some p) (hcode : p.code = true) (hn : 0 < n)
    (hin : a.toNat % 4096 + n ≤ 4096) :
    ∀ acc, MemM1.WitnessIF.AccIF acc → (kmap P).permitted a acc true (n : Int) := by
  intro acc hA
  refine ⟨ha, by omega, by omega, p, hp, ?_⟩
  rw [hcode]
  exact hA

#print axioms evData_K
#print axioms agreesV3_kmapK
#print axioms agreesV3_kmapK_data
#print axioms kmap_permitted
#print axioms kmap_permitted_code
end MemM1.ConsumerV3K
