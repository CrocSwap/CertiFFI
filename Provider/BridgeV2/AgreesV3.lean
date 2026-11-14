import BridgeV2.BoundaryV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.BoundaryV2
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to BridgeV2.AgreesV3LNSym.
namespace ArmCert.Premises.TranslationAgreesV3

/- E17 v3.
   Strengthens TranslationAgreesV1 (v2 684d7557) in the ways the heap memory forms need:
   (1) frame-closed: holds at every state u with the registers and memory of s (MemSingle_*
       makes framed oracle draws before translating);
   (2) per permitted access the actual translation also gives inner+outer Write-Back Normal
       memory, ad.vaddress = va, data accesses leave ALL registers unchanged (IFETCH: the
       projected ones; it writes InGuardedPage), and memory unchanged (no table-byte writes);
   (3) the exact event delta: translationStart ++ W ++ translationEnd ad, W the AK_ttw reads
       whose PA sequence is a public function `walk` of the admitted map (isla derived events).
   STATEMENT ONLY: the instance is memory's (kmap, from eval WalkFactE). -/

/-- One 8-byte translation-table read at pa (kind AK_ttw, tag false); = eval M1a.WEv.IsTTWRead. -/
def TTWRead (pa : Nat) (e : Event) : Prop :=
  ∃ va, e = Event.memRead pa 8 va (.AK_ttw ()) false

/-- The walk reads for va are exactly one TTWRead per PA of `walk va`, in order. -/
def TTWReadsOK (walk : BitVec 64 → List Nat) (va : BitVec 64) (W : Array Event) : Prop :=
  W.size = (walk va).length ∧ ∀ (i : Nat) (h : i < W.size), TTWRead ((walk va).getD i 0) W[i]

/-- E17 v3. `walk va` = the descriptor PAs the walk for va reads (fixed by the admitted map). -/
def TranslationAgrees (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State) : Prop :=
  ∀ u : State, u.regs = s.regs → u.mem = s.mem →
  ∀ va accdesc aligned size, m.permitted va accdesc aligned size →
    ∃ ad t, AArch64_TranslateAddress va accdesc aligned size u = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := m.pa va } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      ad.memattrs.inner.attrs = MemAttr_WB ∧ ad.memattrs.outer.attrs = MemAttr_WB ∧
      ad.vaddress = va ∧
      (accdesc.acctype = .AccessType_IFETCH → ProjRegsEq u.regs t.regs) ∧
      (accdesc.acctype ≠ .AccessType_IFETCH → t.regs = u.regs) ∧
      t.mem = u.mem ∧
      ∃ ti W, t.events = u.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
        TTWReadsOK walk va W

/-- v3 implies the v2 premise (E17 as used by PremisesV2.agrees). -/
theorem toV1 {m : ConsumerMap} {walk : BitVec 64 → List Nat} {s : State}
    (h : TranslationAgrees m walk s) : TranslationAgreesV1.TranslationAgrees m s := by
  intro va accdesc aligned size hp
  rcases h s rfl rfl va accdesc aligned size hp with
    ⟨ad, t, ht, hf, hpa, hmt, _, _, _, hif, hdata, hmem, _⟩
  refine ⟨ad, t, ht, hf, hpa, hmt, ?_, fun a _ => by rw [hmem]⟩
  by_cases hk : accdesc.acctype = .AccessType_IFETCH
  · exact hif hk
  · rw [hdata hk]; exact ProjRegsEq.refl _

/-- Register E-items the data path reads after translation (, isla 924f):
    no SPE sample in flight, little-endian EL0 data (SCTLR_EL2.E0E = 0, already in E3),
    FEAT_MTE2 absent (FeatureImpl[134] = false: closes every tag-check branch of MemSingle_*;
    GB10 shows no mte hwcap), and FEAT_LSE2 present (FeatureImpl[111] = true: a 16-byte
    LDP/STP is ONE single-copy access, CertiFFI Reg_pair_signed_offset). v5: replaces the
    v4 TCF0 pin, which memory's proofs do not use. -/
structure DataPins (s : State) : Prop where
  spe : s.regs.bank_Bool .SPESampleInFlight = false
  e0e : _get_SCTLR_EL2_Type_E0E (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1
  mte2Off : s.regs.FeatureImpl[134] = false
  lse2 : s.regs.FeatureImpl[111] = true
  /-- v6 (, crypto 2596): FEAT_TME absent, so CreateAccDescGPR's
      transactional = HaveTME() && TSTATE.depth > 0 is false. GB10 cores lack FEAT_TME. -/
  tmeOff : s.regs.FeatureImpl[227] = false

end ArmCert.Premises.TranslationAgreesV3

