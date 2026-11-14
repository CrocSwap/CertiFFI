-- Memory (split, d200 P3 memory steps): the two deployment-side binders of the runtime14 memory step
-- facts, agreed with. Both types are case-generic; each case instantiates them with its own constant list.
--  * DataStaticR14 mapping p footprint sites: every data site (base form, size) of the case is mapped to a non-MMIO
--    PA run off the table footprint, aligned to its size, and contiguous.
--  * PinsAgree p rs forms inputs: the pinned entry registers (x0, x1, x19, SP) of the value-layer inputs equal the
--    pins, and every indirect form the case uses is the value the inputs compute for it.
import R14E17.Table
import R14Plan.Plan
import ArmCertValue.ReleaseGen
import MemM1.MemReadIF
import PipeR14.Inst
import ArmCertTranslateModel.C9TranslateBinding
set_option autoImplicit false
namespace PipeR14
open ArmCertValue ArmCert.Translate.Model

/-- VA of byte j of region r under pins p. -/
def regionVA (p : R14E17.Pins) (r : Region) (j : Nat) : BitVec 64 := BitVec.ofInt 64 ((pinv p r.pin : Int) + r.off + j)

/-- The data PAs of a case's sites. -/
def DataPA (mapping : BitVec 64 → Option Nat) (p : R14E17.Pins) (sites : List (R14Plan.Base × Nat)) (a : Nat) : Prop :=
  ∃ s ∈ sites, ∃ t, t < s.2 ∧ mapping (R14E17.dataVA p s.1 + BitVec.ofNat 64 t) = some a

/-- Data statics of a case (the data analogue of CodeStaticR14), over its sites and tracked regions. -/
structure DataStaticR14 (mapping : BitVec 64 → Option Nat) (p : R14E17.Pins) (footprint : Nat → Prop)
    (sites : List (R14Plan.Base × Nat)) (regions : List Region) (sc : Nat → Prop) (base : BitVec 64) : Prop where
  site : ∀ s ∈ sites, ∃ pa : BitVec 56, mapping (R14E17.dataVA p s.1) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
    (∀ t, t < s.2 → ¬ footprint (pa.toNat + t)) ∧ (R14E17.dataVA p s.1).toNat % s.2 = 0 ∧
    (∀ t, t < s.2 → mapping (R14E17.dataVA p s.1 + BitVec.ofNat 64 t) = some (pa.toNat + t))
  sp16 : p.regs 31 % 16 = 0
  code : ImageTableSeparated sc base mapping (DataPA mapping p sites)
  inj : ∀ r ∈ regions, ∀ j, j < 8 * r.words → ∀ s ∈ sites, ∀ t, t < s.2 → ∀ q,
    mapping (regionVA p r j) = some q → mapping (R14E17.dataVA p s.1 + BitVec.ofNat 64 t) = some q →
    regionVA p r j = R14E17.dataVA p s.1 + BitVec.ofNat 64 t
  distinct : ∀ r1 ∈ regions, ∀ r2 ∈ regions, ∀ j1 j2, j1 < 8 * r1.words → j2 < 8 * r2.words →
    regionVA p r1 j1 = regionVA p r2 j2 → r1 = r2 ∧ j1 = j2

/-- VA arithmetic: an Int-level identity gives the BitVec one. -/
theorem va_eq {X Y : Int} (t : Nat) (h : X = Y + t) : BitVec.ofInt 64 X = BitVec.ofInt 64 Y + BitVec.ofNat 64 t := by
  rw [h, BitVec.ofInt_add, BitVec.ofInt_natCast]

/-- A store at site s writing region r's bytes j0 .. j0 + n misses every other tracked region byte. -/
theorem miss_of {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins} {footprint : Nat → Prop}
    {sites : List (R14Plan.Base × Nat)} {regions : List Region} {sc : Nat → Prop} {base : BitVec 64}
    (ds : DataStaticR14 mapping p footprint sites regions sc base) {s : R14Plan.Base × Nat} (hs : s ∈ sites)
    {r : Region} (hr : r ∈ regions) {j0 n : Nat} (hn : n ≤ s.2) (hw : j0 + n ≤ 8 * r.words) {pa : Nat}
    (contig : ∀ t, t < s.2 → mapping (R14E17.dataVA p s.1 + BitVec.ofNat 64 t) = some (pa + t))
    (hva : ∀ t, t < n → R14E17.dataVA p s.1 + BitVec.ofNat 64 t = regionVA p r (j0 + t)) :
    ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words → ¬ (r' = r ∧ j0 ≤ j' ∧ j' < j0 + n) → ∀ q,
      mapping (regionVA p r' j') = some q → ¬ (pa ≤ q ∧ q < pa + n) := by
  intro r' hr' j' hj' nf q hq ⟨lo, hi⟩
  have ht : q - pa < n := by omega
  have hc := contig (q - pa) (by omega)
  rw [show pa + (q - pa) = q by omega] at hc
  have e := ds.inj r' hr' j' hj' s hs (q - pa) (by omega) q hq hc
  rw [hva (q - pa) ht] at e
  obtain ⟨rfl, rfl⟩ := ds.distinct r' hr' r hr j' (j0 + (q - pa)) hj' (by omega) e
  exact nf ⟨rfl, by omega, by omega⟩

/-- The pinned entry registers (index 31 = SP). -/
def pinRegs : List Nat := [0, 1, 19, 31]

/-- Input entry of region byte (g, j) under the region list rs (0 if untracked). -/
def inByte (rs : List (Region × Nat)) (inputs : List (BitVec 64)) (g : Region) (j : Nat) : BitVec 64 :=
  match memBL rs 0 g j with
  | some (i, _) => inputs.getD i 0
  | none => 0

/-- The value an indirect form takes over the inputs (registers after the region bytes; x1obj = region ⟨1, 0, 2⟩). -/
def formVal (rs : List (Region × Nat)) (inputs : List (BitVec 64)) (f : String) : BitVec 64 :=
  let reg := fun i => inputs.getD (totalL rs + i) 0
  if f = "x0+UBFM64[1,63](x1)+24" then reg 0 + (reg 1 >>> 1) + 24#64
  else if f = "x0+mem64[x1+8]+24" then
    reg 0 + Op.eval (.asm8 [0, 0, 0, 0, 0, 0, 0, 0])
      ((List.range 8).map fun t => inByte rs inputs ⟨1, 0, 2⟩ (8 + t)) + 24#64
  else 0#64

def PinsAgree (p : R14E17.Pins) (rs : List (Region × Nat)) (forms : List String) (inputs : List (BitVec 64)) : Prop :=
  (∀ i ∈ pinRegs, inputs.getD (totalL rs + i) 0 = BitVec.ofNat 64 (p.regs i)) ∧
    (∀ f ∈ forms, p.indirect f = (formVal rs inputs f).toNat)

/-- A case's data sites and indirect forms, read off its declared accesses. -/
def sitesOf (accs : List R14E17.Access) : List (R14Plan.Base × Nat) := (accs.map fun a => (a.2.1, a.2.2.1)).eraseDups
def formsOf (accs : List R14E17.Access) : List String :=
  (accs.filterMap fun a => match a.2.1 with | .indirect f => some f | .pin _ _ => none).eraseDups

abbrev dataSites_c00 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c00
abbrev forms_c00 : List String := formsOf R14Plan.accesses_c00
abbrev dataSites_c01 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c01
abbrev forms_c01 : List String := formsOf R14Plan.accesses_c01
abbrev dataSites_c02 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c02
abbrev forms_c02 : List String := formsOf R14Plan.accesses_c02
abbrev dataSites_c03 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c03
abbrev forms_c03 : List String := formsOf R14Plan.accesses_c03
abbrev dataSites_c04 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c04
abbrev forms_c04 : List String := formsOf R14Plan.accesses_c04
abbrev dataSites_c05 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c05
abbrev forms_c05 : List String := formsOf R14Plan.accesses_c05
abbrev dataSites_c06 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c06
abbrev forms_c06 : List String := formsOf R14Plan.accesses_c06
abbrev dataSites_c07 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c07
abbrev forms_c07 : List String := formsOf R14Plan.accesses_c07
abbrev dataSites_c08 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c08
abbrev forms_c08 : List String := formsOf R14Plan.accesses_c08
abbrev dataSites_c09 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c09
abbrev forms_c09 : List String := formsOf R14Plan.accesses_c09
abbrev dataSites_c10 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c10
abbrev forms_c10 : List String := formsOf R14Plan.accesses_c10
abbrev dataSites_c11 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c11
abbrev forms_c11 : List String := formsOf R14Plan.accesses_c11
abbrev dataSites_c12 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c12
abbrev forms_c12 : List String := formsOf R14Plan.accesses_c12
abbrev dataSites_c13 : List (R14Plan.Base × Nat) := sitesOf R14Plan.accesses_c13
abbrev forms_c13 : List String := formsOf R14Plan.accesses_c13

end PipeR14
