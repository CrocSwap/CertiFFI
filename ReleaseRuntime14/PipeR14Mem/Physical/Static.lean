-- physical access-run data certificates. These are derived certificates, not a linear-interior-map premise.
import PipeR14Mem.Static
import ArmCertValue.PhysicalMemory
import PipeR14Mem.Compat.Core
set_option autoImplicit false
namespace PipeR14.Physical
open ArmCertValue ArmCert.Translate.Model
open ArmCertValue.Physical (BytePA spanPA trackedBytes)

def DataPA (mapping : BitVec 64 → Option Nat) (p : R14E17.Pins) (sites : List (R14Plan.Base × Nat)) (a : Nat) : Prop :=
  ∃ s ∈ sites, ∃ pa, mapping (R14E17.dataVA p s.1) = some pa ∧ pa ≤ a ∧ a < pa + s.2

structure DataStaticR14 (mapping : BitVec 64 → Option Nat) (bytePA : BytePA) (p : R14E17.Pins)
    (footprint : Nat → Prop) (sites : List (R14Plan.Base × Nat)) (regions : List Region)
    (sc : Nat → Prop) (base : BitVec 64) : Prop where
  site : ∀ s ∈ sites, ∃ pa : BitVec 56, mapping (R14E17.dataVA p s.1) = some pa.toNat ∧
    MemM1.MemReadIF.NotMMIO pa ∧ (∀ t, t < s.2 → ¬ footprint (pa.toNat + t)) ∧
    (R14E17.dataVA p s.1).toNat % s.2 = 0
  sp16 : p.regs 31 % 16 = 0
  code : ImageTableSeparated sc base mapping (DataPA mapping p sites)
  /-- Construct from actual access anchors and their proven overlap agreement (TranslateSpan). -/
  span : ∀ s ∈ sites, ∀ r ∈ regions, ∀ j0, j0 + s.2 ≤ 8 * r.words →
    (∀ t, t < s.2 → regionVA p r (j0 + t) = R14E17.dataVA p s.1 + BitVec.ofNat 64 t) →
    ∀ t, t < s.2 → bytePA r (j0 + t) = spanPA mapping (R14E17.dataVA p s.1) t
  miss : ∀ s ∈ sites, ∀ r ∈ regions, ∀ j0 n, n ≤ s.2 → j0+n ≤ 8*r.words →
    (∀ t, t < n → regionVA p r (j0+t) = R14E17.dataVA p s.1 + BitVec.ofNat 64 t) →
    ∀ pa, mapping (R14E17.dataVA p s.1) = some pa →
    ∀ r' ∈ regions, ∀ j, j < 8*r'.words → ¬ (r'=r ∧ j0 ≤ j ∧ j < j0+n) →
    ∀ q, bytePA r' j = some q → ¬ (pa ≤ q ∧ q < pa+n)

/-- The miss callback is needed only at an actual data access, not on padding/padding pairs. -/
theorem miss_of {mapping : BitVec 64 → Option Nat} {bytePA : BytePA} {p : R14E17.Pins}
    {footprint : Nat → Prop} {sites : List (R14Plan.Base × Nat)} {regions : List Region}
    {sc : Nat → Prop} {base : BitVec 64}
    (ds : DataStaticR14 mapping bytePA p footprint sites regions sc base)
    {s : R14Plan.Base × Nat} (hs : s ∈ sites) {r : Region} (hr : r ∈ regions) {j0 n pa : Nat}
    (hn : n ≤ s.2) (hw : j0+n ≤ 8*r.words)
    (layout : ∀ t, t < n → regionVA p r (j0+t) = R14E17.dataVA p s.1 + BitVec.ofNat 64 t)
    (mapped : mapping (R14E17.dataVA p s.1) = some pa) :
    ∀ r' ∈ regions, ∀ j, j < 8*r'.words → ¬ (r'=r ∧ j0 ≤ j ∧ j < j0+n) →
    ∀ q, bytePA r' j = some q → ¬ (pa ≤ q ∧ q < pa+n) :=
  ds.miss s hs r hr j0 n hn hw layout pa mapped
#print axioms miss_of
end PipeR14.Physical
