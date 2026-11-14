import MemM1.M1CoreVDWE
import MemM1.ConsumerD
import MemM1.LeafFactsGW
import M1a.WalkEvents
import BridgeV2.AgreesV3
import Pilot.S2Bytes
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.WalkKE
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality S1OuterSetup ArmCert.Eval.JointSAT ArmCert.Eval.M1a MemM1.Witness
open ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv ArmCert.Premises.TranslationAgreesV3
open MemM1.WitnessVDWE (WalkOKVDWR coreVDWE)

/-! E17 v3 data-access instance pieces: the walk's PA sequence `walkK`, the bridge from eval's
`WalkFactE` to the event-tracking walk hypothesis, and the per-access AgreesV3 conjuncts. -/

/-- The 8-byte little-endian descriptor stored at `a` (absent bytes read as 0). -/
def descOf (mem : S1ResourcePath.Memory) (a : Nat) : BitVec 64 :=
  (mem[a + 7]?).getD 0#8 +++ (mem[a + 6]?).getD 0#8 +++ (mem[a + 5]?).getD 0#8 +++
  (mem[a + 4]?).getD 0#8 +++ (mem[a + 3]?).getD 0#8 +++ (mem[a + 2]?).getD 0#8 +++
  (mem[a + 1]?).getD 0#8 +++ (mem[a + 0]?).getD 0#8

theorem descOf_eq (mem : S1ResourcePath.Memory) (a : Nat) (d : BitVec 64)
    (h : S2ByteMemory.DescAt mem a d) : descOf mem a = d := by
  unfold descOf
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide)]
  simp only [Option.getD_some, Nat.reduceMul]
  exact S2Bytes.join64_happend d

/-- **The walk PA sequence** for `va` from registers `r` and memory `mem`: the EL2&0 lower-range
    root slot (TTBR0_EL2, start level 0) and the next three slots, each from the descriptor stored
    at the previous one (4K granule, ee = 0). For the run's map use `walk := walkK s.regs s.mem`. -/
def walkK (r : Regs) (mem : S1ResourcePath.Memory) (va : BitVec 64) : List Nat :=
  let s0 := rootSlot r va
  let s1 := S1ResourcePath.nextSlot va 0 (descOf mem s0.address.toNat)
  let s2 := S1ResourcePath.nextSlot va (0 + 1) (descOf mem s1.address.toNat)
  let s3 := S1ResourcePath.nextSlot va (0 + 1 + 1) (descOf mem s2.address.toNat)
  [s0.address.toNat, s1.address.toNat, s2.address.toNat, s3.address.toNat]

/-- eval's `ReadsAlong` (4 levels from the root slot, ee = 0) gives `TTWReadsOK (walkK r mem)`. -/
theorem readsOK (wp : S1TTWParams) (hee : wp.ee = 0#1) (r : Regs) (mem : S1ResourcePath.Memory)
    (va : BitVec 64) (W : Array Event) (h : ReadsAlong wp va mem 4 0 (rootSlot r va) W) :
    TTWReadsOK (walkK r mem) va W := by
  have hdec : ∀ x, S2FetchFrame.decoded wp.ee x = x := by
    intro x; unfold S2FetchFrame.decoded; rw [hee]; rfl
  cases h with
  | table desc0 h0 rest0 =>
    cases rest0 with
    | table desc1 h1 rest1 =>
      cases rest1 with
      | table desc2 h2 rest2 =>
        cases rest2 with
        | leaf h3 =>
          have e0 := descOf_eq _ _ _ desc0
          subst e0
          simp only [hdec] at desc1 h1
          have e1 := descOf_eq _ _ _ desc1
          subst e1
          simp only [hdec] at desc2 h2
          have e2 := descOf_eq _ _ _ desc2
          subst e2
          simp only [hdec] at h3
          refine ⟨rfl, ?_⟩
          intro i hi
          have hi' : i < 4 := by simpa using hi
          rcases i with _ | _ | _ | _ | i
          · exact h0
          · exact h1
          · exact h2
          · exact h3
          · omega
        | table _ _ rest3 => cases rest3


theorem ok_inj {α : Type} {a b : α} {s t : State}
    (h : (EStateM.Result.ok a s : EStateM.Result (Sail.Error exception) State α) = .ok b t) :
    a = b ∧ s = t := by
  cases h; exact ⟨rfl, rfl⟩

/-- Copy of `ConsumerDW.walkOKVDW_of` (that module imports BridgeV2 consumers not needed here). -/
theorem walkOKVDW_of (s : State) (va D : BitVec 64) (hW : MemM1.WalkFactV.WalkFact s va D)
    (hD : MemM1.ConsumerD.LeafBitsD D) (acc : AccessDescriptor) (hA : Acc0 acc) :
    MemM1.WitnessVDW.WalkOKVDW acc s va (MemM1.LeafFactsG.leafBase D) := by
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
  rcases MemM1.LeafFactsGW.leafGW cur m c.wp D w v.regs hcl hcpas hmair hd128 htg hpie hds haie hcapt
      hD.idx hD.ap hD.cont hlv with ⟨hmt, hin, hout, hap, hapt, hl, hc, hb, _⟩
  have hdD : d = D := hd
  refine ⟨fw, wa, w, d, x, hwalk, hfw, hwr, hwm, ?_, ?_, hmt, hin, hout, hl, hc, hb, hap, hapt⟩
  · rw [hdD]; exact hD.af
  · rw [hdD]; exact hD.b7

theorem walkOKVDWR_regs {acc : AccessDescriptor} {s u : State} {va : BitVec 64} {B : BitVec 56}
    {R : Array Event → Prop} (h : WalkOKVDWR acc s va B R) (hr : u.regs = s.regs) (hm : u.mem = s.mem) :
    WalkOKVDWR acc u va B R := by
  unfold WalkOKVDWR at h ⊢
  rw [hr, hm]
  exact h

/-- **Bridge**: eval's `WalkFactE` + data-leaf bits + an EL0 NS GPR access ⇒ the event-tracking walk
    hypothesis, with the walk's reads `TTWReadsOK (walkK s.regs s.mem) va`. -/
theorem walkOKVDWR_of (s : State) (va D : BitVec 64) (hWE : WalkFactE s va D)
    (hD : MemM1.ConsumerD.LeafBitsD D) (acc : AccessDescriptor) (hA : Acc0 acc) :
    WalkOKVDWR acc s va (MemM1.LeafFactsG.leafBase D) (TTWReadsOK (walkK s.regs s.mem) va) := by
  have hO := walkOKVDW_of s va D hWE.walkFact hD acc hA
  intro t htr htm
  rcases hO t htr htm with ⟨wp, u, hg, hfr, a1, a2, a3, a4, a5, a6, a7, hwk⟩
  refine ⟨wp, u, hg, hfr, a1, a2, a3, a4, a5, a6, a7, fun f' v hf' hvr hvm => ?_⟩
  rcases hwk f' v hf' hvr hvm with ⟨fw, wa, w, d, u', hw, hfw, hr, hm, rest⟩
  rcases hWE t htr htm f' acc hf' hA.ss with ⟨wp2, u2, hg2, _, hF2, _, Hv⟩
  obtain rfl : wp2 = wp := (ok_inj (hg2.symm.trans hg)).1
  rcases Hv v (hvr.trans htr.symm) (hvm.trans htm.symm) with
    ⟨c, r, w2, hcwp, hcacc, _, _, hw2, _, W, hWev, hWs, hRA⟩
  have hu : u' = w2 := by
    have := hw.symm.trans hw2
    cases this; rfl
  subst hu
  rw [hvm] at hRA
  exact ⟨fw, wa, w, d, u', hw, hfw, hr, hm, ⟨W, hWev, readsOK _ hF2.1 s.regs s.mem va W hRA⟩, rest⟩

/-- **The AgreesV3 conjuncts for one data access**, on any state `u` with `s`'s registers and
    memory: no fault, PA `{NS, pageOA (leafBase D) va}`, Normal inner/outer WB, `vaddress = va`,
    registers and memory unchanged, and the exact event delta translationStart ++ W ++
    translationEnd with `TTWReadsOK (walkK s.regs s.mem) va W`. -/
theorem tr_dataE (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (va : BitVec 64) (hva : va.toNat < 2^48) (D : BitVec 64) (hWE : WalkFactE s va D)
    (hD : MemM1.ConsumerD.LeafBitsD D) (acc : AccessDescriptor) (hA : Acc0 acc) (aligned : Bool)
    (size : Int) (u : State) (hu : u.regs = s.regs) (hum : u.mem = s.mem) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size u = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := MemM1.VA.pageOA (MemM1.LeafFactsG.leafBase D) va } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      ad.memattrs.inner.attrs = MemAttr_WB ∧ ad.memattrs.outer.attrs = MemAttr_WB ∧
      ad.vaddress = va ∧
      (acc.acctype = .AccessType_IFETCH → ArmCert.Premises.TranslationAgreesV1.ProjRegsEq u.regs t.regs) ∧
      (acc.acctype ≠ .AccessType_IFETCH → t.regs = u.regs) ∧
      t.mem = u.mem ∧
      ∃ ti W, t.events = u.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
        TTWReadsOK (walkK s.regs s.mem) va W := by
  rcases coreVDWE _ va hva _ (MemM1.ConsumerV2.leafBase_and D) acc aligned size u (by rw [hu]; exact hR) hA
      (walkOKVDWR_regs (walkOKVDWR_of s va D hWE hD acc hA) hu hum) (by rw [hu]; exact hC) with
    ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv, hr, hm, ti, W, he, hRW⟩
  refine ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv, fun hk => absurd hk (by rw [hA.gpr]; intro h; cases h),
    fun _ => hr, hm, ti, W, he, hRW⟩

#print axioms descOf_eq
#print axioms readsOK
#print axioms walkOKVDWR_of
#print axioms tr_dataE
end MemM1.WalkKE
