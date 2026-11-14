import MemM1.ConsumerV2
import MemM1.M1CoreVD
import MemM1.LeafFactsGD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace MemM1.ConsumerD
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality S1OuterSetup ArmCert.Eval.JointSAT ArmCert.Eval.M1a MemM1.Witness MemM1.WalkFactV
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2 MemM1.ConsumerV2

/-- Raw-bit facts on a stored level-3 DATA page descriptor, DBM unconstrained (FEAT_HAFDBS dirty
    writable pages: AP = 01, so AP[2] = bit 7 = 0 and the hardware dirty update is the identity). -/
structure LeafBitsD (D : BitVec 64) : Prop where
  idx : Sail.BitVec.extractLsb D 4 2 = 0#3 ∨ Sail.BitVec.extractLsb D 4 2 = 1#3
  ap : Sail.BitVec.extractLsb D 7 6 = 1#2
  af : D.getLsbD 10 = true
  b7 : D.getLsbD 7 = false
  cont : Sail.BitVec.access D 52 = 0#1

/-- The DBM = 0 leaf bits are a special case. -/
theorem LeafBits.toD {D : BitVec 64} (h : LeafBits D) (h7 : D.getLsbD 7 = false) : LeafBitsD D :=
  ⟨h.idx, h.ap, h.af, h7, h.cont⟩

theorem walkOKVD_of (s : State) (va D : BitVec 64) (hW : WalkFact s va D) (hD : LeafBitsD D)
    (acc : AccessDescriptor) (hA : Acc0 acc) :
    MemM1.WitnessVD.WalkOKVD acc s va (MemM1.LeafFactsG.leafBase D) := by
  intro t htr htm
  let f0 : FaultRecord := { (default : FaultRecord) with statuscode := .Fault_None }
  rcases hW t htr htm f0 acc rfl hA.ss with ⟨wp, u, hg, hfr, hF, hAct, _⟩
  rcases hF with ⟨hee, hwxn, _, _, hpie, _, he0pd, _⟩
  rcases hAct with ⟨htg, hd128, haie, hds, hmair, htx, _⟩
  refine ⟨wp, u, hg, hfr, hd128, hpie, hds, htg, htx, hwxn, he0pd, ?_⟩
  intro f' v hf' hvr hvm
  rcases hW t htr htm f' acc hf' hA.ss with ⟨wp', u', hg', _, _, _, Hv⟩
  obtain rfl : wp' = wp := (ok_inj (hg'.symm.trans hg)).1
  rcases Hv v (hvr.trans htr.symm) (hvm.trans htm.symm) with
    ⟨c, ⟨fw, wa, w, d⟩, x, hcwp, _, _, _, hwalk, hwr, hwm, hd, hfw, _, cur, m, hcl, hcpas, hcapt, _, _, hlv⟩
  subst hcwp
  have hdec : S2FetchFrame.decoded c.wp.ee D = D := by
    unfold S2FetchFrame.decoded; rw [hee]; rfl
  rw [hdec] at hd hlv
  rcases MemM1.LeafFactsGD.leafGD cur m c.wp D w v.regs hcl hcpas hmair hd128 htg hpie hds haie hcapt
      hD.idx hD.ap hD.cont hlv with ⟨hmt, hap, hapt, hl, hc, hb, _⟩
  have hdD : d = D := hd
  refine ⟨fw, wa, w, d, x, hwalk, hfw, hwr, hwm, ?_, ?_, hmt, hl, hc, hb, hap, hapt⟩
  · rw [hdD]; exact hD.af
  · rw [hdD]; exact hD.b7

/-- agreesK with DBM unconstrained on data pages (Linux HAFDBS dirty writable pages). -/
theorem agreesKD (s : State) (hR : Regs20 s.regs) (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFact s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf)) :
    TranslationAgrees (kmap P) s := by
  intro va acc aligned size ⟨hva, _, _, p, hp, hacc⟩
  rcases hP va p hva hp with ⟨hW, hD⟩
  rw [pa_eq P va p hp]
  cases hc : p.code
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hacc hD
    rcases MemM1.WitnessVD.coreVD va hva _ (leafBase_and p.leaf) acc aligned size s hR hacc
        (walkOKVD_of s va p.leaf hW hD acc hacc) with
      ⟨ad, t, h, hf, hpa, hmt, hr, hm⟩
    refine ⟨ad, t, h, hf, hpa, hmt, ?_, fun a _ => by rw [hm]⟩
    rw [hr]; exact ProjRegsEq.refl _
  · simp only [hc, ↓reduceIte] at hacc hD
    rcases MemM1.WitnessIF.coreIF va hva _ (leafBase_and p.leaf) acc aligned size s hR hacc
        (walkOKIF_of s va p.leaf hW hD acc hacc) with
      ⟨ad, t, h, hf, hpa, hmt, hr, hm⟩
    refine ⟨ad, t, h, hf, hpa, hmt, ?_, fun a _ => by rw [hm]⟩
    rw [hr]; exact projRegsEq_clrGP _

/-- A dirty, writable Linux user page (DBM = 1, AP = 01, AF = 1, AttrIndx 0) meets LeafBitsD. -/
theorem dirty_example : LeafBitsD 0x0008000505000443#64 :=
  ⟨Or.inl (by decide), by decide, by decide, by decide, by decide⟩

#print axioms walkOKVD_of
#print axioms agreesKD
#print axioms dirty_example
end MemM1.ConsumerD
