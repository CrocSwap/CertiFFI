import MemM1.ConsumerDW
import BridgeV2.AgreesV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
namespace MemM1.ConsumerV3
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.Witness MemM1.WalkFactV MemM1.WitnessIF
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2 MemM1.ConsumerV2 MemM1.ConsumerD
open ArmCert.Premises.TranslationAgreesV3 (TTWReadsOK)

abbrev AgreesV3 := ArmCert.Premises.TranslationAgreesV3.TranslationAgrees

/-! E17 v3 instance shell for the page-keyed map `kmap`.

Proved here (from `WitnessVDW.coreVDW`, `WitnessIF.coreIF`, Regs20, SCTLR_EL2.C = 1 and the
per-page WalkFact + LeafBitsD/LeafBitsC): every permitted access translates with no fault to
{NS, kmap.pa va}, Normal; data accesses additionally give inner/outer WB, `vaddress = va`, all
registers and memory unchanged; IFETCH gives ProjRegsEq (clrGP) and memory unchanged.

Taken as hypotheses (the per-access event-tracking cores, not yet available):
* `EvData walk s P`: for a data access on a data page, the TranslateAddress result's event delta
  is `translationStart ti ++ W ++ translationEnd ad` with `TTWReadsOK walk va W`
  (the event clause of the data core coreVDWE being built in parallel; by determinism of
  TranslateAddress it is a statement about whatever result the call returns).
* `EvIF walk s P`: the same for IFETCH on a code page, plus inner/outer WB and `vaddress = va`
  (coreIFE gives `vaddress` and the events; WB for IFETCH needs SCTLR_EL2.I = 1 and an
  attribute-tracking IFETCH S1Translate, not yet proved). -/

def EvData (walk : BitVec 64 → List Nat) (s : State) (P : BitVec 64 → Option Page) : Prop :=
  ∀ u : State, u.regs = s.regs → u.mem = s.mem →
  ∀ (va : BitVec 64) (p : Page) (acc : AccessDescriptor) (aligned : Bool) (size : Int)
    (ad : AddressDescriptor) (t : State),
    va.toNat < 2^48 → P (va >>> 12) = some p → p.code = false → Acc0 acc →
    AArch64_TranslateAddress va acc aligned size u = .ok ad t →
    ∃ ti W, t.events = u.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
      TTWReadsOK walk va W

def EvIF (walk : BitVec 64 → List Nat) (s : State) (P : BitVec 64 → Option Page) : Prop :=
  ∀ u : State, u.regs = s.regs → u.mem = s.mem →
  ∀ (va : BitVec 64) (p : Page) (acc : AccessDescriptor) (aligned : Bool) (size : Int)
    (ad : AddressDescriptor) (t : State),
    va.toNat < 2^48 → P (va >>> 12) = some p → p.code = true → AccIF acc →
    AArch64_TranslateAddress va acc aligned size u = .ok ad t →
    ad.memattrs.inner.attrs = MemAttr_WB ∧ ad.memattrs.outer.attrs = MemAttr_WB ∧
    ad.vaddress = va ∧
    ∃ ti W, t.events = u.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
      TTWReadsOK walk va W

theorem walkOKIF_regs {acc : AccessDescriptor} {s u : State} {va : BitVec 64} {B : BitVec 56}
    (h : WalkOKIF acc s va B) (hr : u.regs = s.regs) (hm : u.mem = s.mem) :
    WalkOKIF acc u va B := by
  unfold WalkOKIF at h ⊢
  rw [hr, hm]
  exact h

/-- **E17 v3 for `kmap`** (shell: event clauses, and IFETCH attributes/vaddress, as hypotheses). -/
theorem agreesV3_kmap (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option Page) (walk : BitVec 64 → List Nat)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFact s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf))
    (hEvD : EvData walk s P) (hEvI : EvIF walk s P) :
    AgreesV3 (kmap P) walk s := by
  intro u hu hum va acc aligned size ⟨hva, _, _, p, hp, hacc⟩
  rcases hP va p hva hp with ⟨hW, hD⟩
  rw [pa_eq P va p hp]
  cases hc : p.code
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hacc hD
    rcases MemM1.ConsumerDW.tr_data s hR hC va hva p.leaf hW hD acc hacc aligned size u hu hum with
      ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv, hr, hm⟩
    have hnif : acc.acctype ≠ .AccessType_IFETCH := by rw [hacc.gpr]; intro e; cases e
    refine ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv, fun e => absurd e hnif, fun _ => hr, hm, ?_⟩
    exact hEvD u hu hum va p acc aligned size ad t hva hp hc hacc h
  · simp only [hc, ↓reduceIte] at hacc hD
    rcases MemM1.WitnessIF.coreIF va hva _ (leafBase_and p.leaf) acc aligned size u
        (by rw [hu]; exact hR) hacc
        (walkOKIF_regs (MemM1.WalkFactV.walkOKIF_of s va p.leaf hW hD acc hacc) hu hum) with
      ⟨ad, t, h, hf, hpa, hmt, hr, hm⟩
    rcases hEvI u hu hum va p acc aligned size ad t hva hp hc hacc h with ⟨hin, hout, hv, hev⟩
    refine ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv, fun _ => ?_, fun e => absurd hacc.ifetch e, hm, hev⟩
    rw [hr]; exact projRegsEq_clrGP _

/-- With only data pages, the IFETCH hypothesis is vacuous. -/
theorem evIF_of_data (walk : BitVec 64 → List Nat) (s : State) (P : BitVec 64 → Option Page)
    (hdata : ∀ n p, P n = some p → p.code = false) : EvIF walk s P := by
  intro u _ _ va p _ _ _ _ _ _ hp hc
  rw [hdata _ p hp] at hc; cases hc

#print axioms walkOKIF_regs
#print axioms agreesV3_kmap
#print axioms evIF_of_data
end MemM1.ConsumerV3
