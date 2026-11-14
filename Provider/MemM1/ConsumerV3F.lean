import MemM1.ConsumerV3K
import MemM1.TrIFE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace MemM1.ConsumerV3F
abbrev State := SequentialState Regs oracleChoiceSource
open MemM1.Witness MemM1.WalkFactV MemM1.ConsumerV2 MemM1.ConsumerD MemM1.ConsumerV3 MemM1.ConsumerV3K
open ArmCert.Eval.M1a.WEv (WalkFactE)
open MemM1.WalkKE (walkK)

/-- E17 v3 (AgreesV3) for the page-keyed map with data AND code pages: no event hypothesis left.
    Data pages: LeafBitsD (DBM free on dirty AP=01 pages); code pages: LeafBitsC. Premises on the
    state: Regs20 bit predicates, SCTLR_EL2.C = 1 and SCTLR_EL2.I = 1 (eval E3), and eval's
    WalkFactE per mapped VA (translate_walk_path_evT). walk = the 4 slot PAs read from the tables. -/
theorem agreesV3_kmapK_full (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFactE s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf)) :
    ArmCert.Premises.TranslationAgreesV3.TranslationAgrees (kmap P) (walkK s.regs s.mem) s :=
  agreesV3_kmapK s hR hC P hP
    (MemM1.TrIFE.evIF_kmap s hR hI P (fun va p hva hp hc => by
      rcases hP va p hva hp with ⟨hW, hD⟩
      simp only [hc, ↓reduceIte] at hD
      exact ⟨hW, hD⟩))

#print axioms agreesV3_kmapK_full
end MemM1.ConsumerV3F
