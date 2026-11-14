import MemM1.PairAfter
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemSingle8V5
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2 MemM1.MemWriteD1
open MemM1.MemWriteD4 MemM1.MemWriteD5 MemM1.MemWriteD6 MemM1.MemWriteD7 MemM1.MemDataV3 MemM1.MemDataV5
open MemM1.MemInv
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
open ArmCert.Premises.TranslationAgreesV3 (TTWReadsOK DataPins)
open MemM1.ConsumerV2 (Page)
open MemM1.ConsumerB (kmapB walkB)

/-- `Mem_read a 8 acc` (8-aligned, tagchecked free, MTE2 absent): one 8-byte access. -/
theorem memRead2_8 (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (s : State)
    (pa : BitVec 56) (data : BitVec (8 * 8)) (hA : AccDR2 acc) (hM2 : s.regs.FeatureImpl[134] = false)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_read a 8 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 8 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((8 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  obtain ⟨lse, e5⟩ : ∃ b, HaveLSE2Ext () s3 = .ok b s3 := ⟨_, rfl⟩
  rcases single2_8 a halign acc s3 pa data hA (by rw [F3.1]; exact hM2) Q
      (fun u fu => hTA u (frame_trans F3 fu)) hio with
    ⟨ad, t1, t, hQ, hP, e6, hte, htr, htm⟩
  have hPt : PostRegs t.regs := htr ▸ hP.post
  rcases MemM1.MemReadDBE.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0 hPt.ns hPt.e2h
    hPt.tge hPt.e0e with ⟨t', e7, f7⟩
  have hal := MemM1.MemReadD.isAligned8 a halign
  have hai := MemM1.MemReadD.allIn8 a halign s3
  have hsz2 : (((((8 : Nat) == 1 || (8 : Nat) == 2) || (8 : Nat) == 4) || (8 : Nat) == 8) || (8 : Nat) == 16) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  refine ⟨ad, t1, t', hQ, ?_, f7.2.2.trans hte, f7.1.trans htr, f7.2.1.trans htm⟩
  cases lse <;>
  · unfold Mem_read Mem_read__2
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz2, e1, e2, e3, e4, e5, e6, hA.gpr, e7, hal, hai, hga, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
      ↓reduceIte, ite_self, Sail.BitVec.castWidth_eq]

/-- **LDR 64-bit (`Mem_read a 8 acc`, 8-aligned) on E17 v3 + DataPins v5**, events fully pinned. -/
theorem readV5_ldr8 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : m.permitted a acc true ((8 : Nat) : Int)) (hio : NotMMIO (m.pa a))
    (data : BitVec (8 * 8))
    (hmem : ∀ i < 8, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad ti W t, Mem_read a 8 acc s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead (m.pa a).toNat 8 (some a.toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  have hif := gpr_not_if hA.gpr
  have hP := postRegs2_v5 s hD hB
  rcases memRead2_8 a halign acc s (m.pa a) data hA hP.noMTE2 _
      (tr_of (dataMap m) s (e17s_of hT) hP a acc 8 ⟨hp, hif⟩ data hmem) hio with
    ⟨ad, t1, t, ⟨u, fu, h1, hv, hr, hm⟩, h, hte, htr, htm⟩
  rcases events_of hT a acc true _ hp u fu ad t1 h1 with ⟨ti, W, hev1, hW⟩
  exact ⟨ad, ti, W, t, h, by rw [hte, kind_eq2 acc hA, hv, hev1, push_end], hW, htr.trans hr,
    htm.trans hm⟩

/-- **STR 64-bit (`Mem_set a 8 acc v`, 8-aligned) on E17 v3 + DataPins v5**, events fully pinned. -/
theorem strV5_8 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (v : BitVec (8 * 8))
    (hA : AccDWT acc)
    (hp : m.permitted a acc true ((8 : Nat) : Int)) (hio : NotMMIO (m.pa a)) :
    ∃ ad ti W t, Mem_set a 8 acc v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite (m.pa a).toNat 8 (some a.toNat) akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 8) v)) none] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧
      t.mem = wfold s.mem (m.pa a).toNat 8 (wbyte v) ∧
      (∀ p, t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + 8
        then some (wbyte v (p - (m.pa a).toNat)) else s.mem[p]?) := by
  have hif := gpr_not_if hA.base.gpr
  have h8 : SizeOK 8 := by unfold SizeOK; omega
  rcases memset_strongT a 8 h8 halign acc s v hA (m.pa a) (preW_v5 acc s hD hB) hD.spe
      (strongTA_of hT a acc 8 hp hif) hio with ⟨u, ad, t1, t, fu, h1, h, hev, hr, hm, hget⟩
  rcases events_of hT a acc true _ hp u fu ad t1 h1 with ⟨ti, W, hev1, hW⟩
  exact ⟨ad, ti, W, t, h, by rw [hev, hev1, push_end], hW, hr, hm, hget⟩

/-- **LDR 64-bit on memory's run invariant.** -/
theorem readV5_ldr8_inv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (hI : MemInv s0 P4 P2 TB s) (hB : BEPins s.regs)
    (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : (kmapB P4 P2).permitted a acc true ((8 : Nat) : Int)) (hio : NotMMIO ((kmapB P4 P2).pa a))
    (data : BitVec (8 * 8))
    (hmem : ∀ i < 8, s.mem[((kmapB P4 P2).pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad ti W t, Mem_read a 8 acc s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead ((kmapB P4 P2).pa a).toNat 8 (some a.toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) a W ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  rcases memInv_agrees s0 P4 P2 TB s hI with ⟨hT, _, hD⟩
  exact readV5_ldr8 _ _ s hT hD hB a halign acc hA hp hio data hmem

/-- **STR 64-bit on memory's run invariant.** -/
theorem strV5_8_inv (s0 : State) (P4 P2 : BitVec 64 → Option Page) (TB : Nat → Prop) (s : State)
    (hI : MemInv s0 P4 P2 TB s) (hB : BEPins s.regs)
    (a : BitVec 64) (halign : a.toNat % 8 = 0) (acc : AccessDescriptor) (v : BitVec (8 * 8))
    (hA : AccDWT acc)
    (hp : (kmapB P4 P2).permitted a acc true ((8 : Nat) : Int)) (hio : NotMMIO ((kmapB P4 P2).pa a)) :
    ∃ ad ti W t, Mem_set a 8 acc v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite ((kmapB P4 P2).pa a).toNat 8 (some a.toNat) akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 8) v)) none] ∧
      TTWReadsOK (walkB s0.regs s0.mem P2) a W ∧ t.regs = s.regs ∧
      t.mem = wfold s.mem ((kmapB P4 P2).pa a).toNat 8 (wbyte v) ∧
      (∀ p, t.mem[p]? = if ((kmapB P4 P2).pa a).toNat ≤ p ∧ p < ((kmapB P4 P2).pa a).toNat + 8
        then some (wbyte v (p - ((kmapB P4 P2).pa a).toNat)) else s.mem[p]?) := by
  rcases memInv_agrees s0 P4 P2 TB s hI with ⟨hT, _, hD⟩
  exact strV5_8 _ _ s hT hD hB a halign acc v hA hp hio

#print axioms memRead2_8
#print axioms readV5_ldr8
#print axioms strV5_8
#print axioms readV5_ldr8_inv
#print axioms strV5_8_inv
end MemM1.MemSingle8V5
