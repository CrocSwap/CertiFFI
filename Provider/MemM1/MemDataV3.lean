import MemM1.MemReadD2
import MemM1.MemWriteD7
import BridgeV2.AgreesV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemDataV3
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2 MemM1.MemWriteD1 MemM1.MemWriteD4 MemM1.MemWriteD5 MemM1.MemWriteD6 MemM1.MemWriteD7
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
open ArmCert.Premises.TranslationAgreesV3 (TTWReadsOK DataPins)

abbrev AgreesV3 := ArmCert.Premises.TranslationAgreesV3.TranslationAgrees

/-! Data read/write lemmas re-targeted to eval's sealed E17 v3 (`TranslationAgreesV3`) +
`DataPins`, with the event log fully pinned:
`t.events = s.events ++ #[translationStart ti] ++ W ++ #[translationEnd ad, memRead/memWrite …]`,
`TTWReadsOK walk a W`.

Extra register hypotheses beyond AgreesV3 + DataPins (BigEndian inputs + MTE closure):
* `BEPins s.regs`: PSTATE.EL = 0, PSTATE.nRW = 0, FeatureImpl[232] (RME) = false,
  FeatureImpl[54] (VHE) = true, FeatureImpl[4] (AArch64 EL0) = true, SCR_EL3.NS = 1,
  HCR_EL2.E2H = 1, HCR_EL2.TGE = 1. (PremisesV2 already has PSTATE.EL = 0; the others are the
  `Witness.Regs20` bits plus nRW.)
* `hMTE2 : FeatureImpl[134] = false` (FEAT_MTE2 absent) in place of DataPins.tcf0, which the
  proofs do not use. -/

/-- The BigEndian inputs read by the data path (none is in DataPins). -/
structure BEPins (r : Regs) : Prop where
  el0 : r.PSTATE.EL = 0#2
  nrw : r.PSTATE.nRW = 0#1
  noRME : r.FeatureImpl[232] = false
  vhe : r.FeatureImpl[54] = true
  aa64el0 : r.FeatureImpl[4] = true
  ns : Sail.BitVec.extractLsb (r.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1
  e2h : Sail.BitVec.extractLsb (r.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1
  tge : Sail.BitVec.extractLsb (r.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1

/-- `Witness.Regs20` plus PSTATE.nRW = 0 gives BEPins. -/
theorem BEPins.of_regs20 {r : Regs} (h : MemM1.Witness.Regs20 r) (hnrw : r.PSTATE.nRW = 0#1) :
    BEPins r :=
  ⟨h.el0, hnrw, h.noRME, h.vhe, h.aa64el0, h.ns, h.e2h, h.tge⟩

theorem e0e_of (s : State) (hD : DataPins s) :
    Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1 := hD.e0e

theorem postRegs2_of (s : State) (hD : DataPins s) (hB : BEPins s.regs)
    (hMTE2 : s.regs.FeatureImpl[134] = false) : PostRegs2 s.regs :=
  ⟨⟨hD.spe, hB.el0, hB.nrw, hB.noRME, hB.vhe, hB.aa64el0, hB.ns, hB.e2h, hB.tge, e0e_of s hD⟩, hMTE2⟩

theorem preW_of (acc : AccessDescriptor) (s : State) (hD : DataPins s) (hB : BEPins s.regs)
    (hMTE2 : s.regs.FeatureImpl[134] = false) : PreW acc s.regs :=
  ⟨hB.el0, hB.nrw, hB.noRME, hB.vhe, hB.aa64el0, hB.ns, hB.e2h, hB.tge, e0e_of s hD,
    Or.inr hMTE2⟩

theorem postW_of (acc : AccessDescriptor) (s : State) (hD : DataPins s)
    (hMTE2 : s.regs.FeatureImpl[134] = false) : PostW acc s.regs :=
  ⟨hD.spe, Or.inr hMTE2⟩

/-- The data (non-IFETCH) part of a consumer map: same PA function, permits only data accesses. -/
def dataMap (m : ConsumerMap) : ConsumerMap :=
  { m with permitted := fun va acc al sz => m.permitted va acc al sz ∧ acc.acctype ≠ .AccessType_IFETCH }

/-- E17 v3 gives the read side's E17S for the data part of the map. -/
theorem e17s_of {m : ConsumerMap} {walk : BitVec 64 → List Nat} {s : State}
    (h : AgreesV3 m walk s) : E17S (dataMap m) s := by
  refine ⟨fun u hu hum va acc al sz ⟨hp, hif⟩ => ?_⟩
  rcases h u hu hum va acc al sz hp with
    ⟨ad, t, ht, hf, hpa, hmt, hin, hout, hv, _, hdata, hm, _⟩
  exact ⟨ad, t, ht, hf, hpa, hmt, hin, hout, hv, hdata hif, hm⟩

/-- E17 v3 gives the write side's StrongTA for a permitted data access. -/
theorem strongTA_of {m : ConsumerMap} {walk : BitVec 64 → List Nat} {s : State}
    (h : AgreesV3 m walk s) (a : BitVec 64) (acc : AccessDescriptor) (n : Nat)
    (hp : m.permitted a acc true (n : Int)) (hif : acc.acctype ≠ .AccessType_IFETCH) :
    StrongTA a acc n (m.pa a) s := by
  intro u hu hum
  rcases h u hu hum a acc true _ hp with ⟨ad, t, ht, hf, hpa, hmt, _, _, hv, _, hdata, hm, _⟩
  exact ⟨ad, t, ht, hf, hpa, hmt, hv, hdata hif, hm⟩

/-- E17 v3's walk-event delta for a translation run from a framed state. -/
theorem events_of {m : ConsumerMap} {walk : BitVec 64 → List Nat} {s : State}
    (h : AgreesV3 m walk s) (a : BitVec 64) (acc : AccessDescriptor) (al : Bool) (n : Int)
    (hp : m.permitted a acc al n) (u : State) (fu : Frame s u) (ad : AddressDescriptor) (t1 : State)
    (hta : AArch64_TranslateAddress a acc al n u = .ok ad t1) :
    ∃ ti W, t1.events = s.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
      TTWReadsOK walk a W := by
  rcases h u fu.1 fu.2.1 a acc al n hp with ⟨ad', t', ht, _, _, _, _, _, _, _, _, _, ti, W, hev, hW⟩
  rw [hta] at ht
  injection ht with had ht'
  subst had ht'
  exact ⟨ti, W, by rw [hev, fu.2.2], hW⟩

theorem push_end (A W : Array Event) (x y z : Event) :
    (A ++ #[x] ++ W ++ #[y]).push z = A ++ #[x] ++ W ++ #[y, z] := by
  apply Array.toList_inj.mp
  simp

theorem gpr_not_if {acc : AccessDescriptor} (h : acc.acctype = .AccessType_GPR) :
    acc.acctype ≠ .AccessType_IFETCH := by rw [h]; intro e; cases e

/-- **LDRB (`Mem_read a 1 acc`) on E17 v3**, events fully pinned. -/
theorem readV3_ldrb (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (hMTE2 : s.regs.FeatureImpl[134] = false)
    (a : BitVec 64) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : m.permitted a acc true ((1 : Nat) : Int)) (hio : NotMMIO (m.pa a))
    (data : BitVec (1 * 8))
    (hmem : ∀ i < 1, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad ti W t, Mem_read a 1 acc s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead (m.pa a).toNat 1 (some a.toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  have hif := gpr_not_if hA.gpr
  rcases readD2_ldrb (dataMap m) s (e17s_of hT) (postRegs2_of s hD hB hMTE2) a acc hA ⟨hp, hif⟩ hio
      data hmem with ⟨u, ad, t1, t, fu, h1, h, hev, hr, hm⟩
  rcases events_of hT a acc true _ hp u fu ad t1 h1 with ⟨ti, W, hev1, hW⟩
  exact ⟨ad, ti, W, t, h, by rw [hev, hev1, push_end]; rfl, hW, hr, hm⟩

/-- **LDP 64-bit with FEAT_LSE2 (`Mem_read__1 a 16 acc true`) on E17 v3**, events fully pinned. -/
theorem readV3_ldp_lse2 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (hMTE2 : s.regs.FeatureImpl[134] = false) (hLSE2 : s.regs.FeatureImpl[111] = true)
    (a : BitVec 64) (halign : a.toNat % 16 = 0) (acc : AccessDescriptor) (hA : AccDR2 acc)
    (hp : m.permitted a acc true ((16 : Nat) : Int)) (hio : NotMMIO (m.pa a))
    (data : BitVec (16 * 8))
    (hmem : ∀ i < 16, s.mem[(m.pa a).toNat + i]? = some (data.extractLsb' (8 * i) 8)) :
    ∃ ad ti W t, Mem_read__1 a 16 acc true s = .ok data t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead (m.pa a).toNat 16 (some a.toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  have hif := gpr_not_if hA.gpr
  rcases readD2_ldp_lse2 (dataMap m) s (e17s_of hT) (postRegs2_of s hD hB hMTE2) hLSE2 a halign acc
      hA ⟨hp, hif⟩ hio data hmem with ⟨u, ad, t1, t, fu, h1, h, hev, hr, hm⟩
  rcases events_of hT a acc true _ hp u fu ad t1 h1 with ⟨ti, W, hev1, hW⟩
  exact ⟨ad, ti, W, t, h, by rw [hev, hev1, push_end]; rfl, hW, hr, hm⟩

/-- **STRB (`Mem_set a 1 acc v`) on E17 v3**, events fully pinned. -/
theorem strbV3 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (hMTE2 : s.regs.FeatureImpl[134] = false)
    (a : BitVec 64) (acc : AccessDescriptor) (v : BitVec (1 * 8)) (hA : AccDWT acc)
    (hp : m.permitted a acc true ((1 : Nat) : Int)) (hio : NotMMIO (m.pa a)) :
    ∃ ad ti W t, Mem_set a 1 acc v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite (m.pa a).toNat 1 (some a.toNat) akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 1) v)) none] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧
      t.mem = wfold s.mem (m.pa a).toNat 1 (wbyte v) ∧
      (∀ p, t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + 1
        then some (wbyte v (p - (m.pa a).toNat)) else s.mem[p]?) := by
  have hif := gpr_not_if hA.base.gpr
  rcases strb_strong a acc s v hA (m.pa a) (preW_of acc s hD hB hMTE2) hD.spe
      (strongTA_of hT a acc 1 hp hif) hio with ⟨u, ad, t1, t, fu, h1, h, hev, hr, hm, hget⟩
  rcases events_of hT a acc true _ hp u fu ad t1 h1 with ⟨ti, W, hev1, hW⟩
  exact ⟨ad, ti, W, t, h, by rw [hev, hev1, push_end], hW, hr, hm, hget⟩

/-- **STP 64-bit with FEAT_LSE2 (`Mem_set__1 a 16 acc true v`) on E17 v3**, events fully pinned. -/
theorem stpV3_lse2 (m : ConsumerMap) (walk : BitVec 64 → List Nat) (s : State)
    (hT : AgreesV3 m walk s) (hD : DataPins s) (hB : BEPins s.regs)
    (hMTE2 : s.regs.FeatureImpl[134] = false) (hLSE : s.regs.FeatureImpl[111] = true)
    (a : BitVec 64) (ha : a.toNat % 16 = 0) (acc : AccessDescriptor) (v : BitVec (16 * 8))
    (hA : AccDWT acc)
    (hp : m.permitted a acc true ((16 : Nat) : Int)) (hio : NotMMIO (m.pa a)) :
    ∃ ad ti W t, Mem_set__1 a 16 acc true v s = .ok () t ∧
      t.events = s.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite (m.pa a).toNat 16 (some a.toNat) akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) v)) none] ∧
      TTWReadsOK walk a W ∧ t.regs = s.regs ∧
      t.mem = wfold s.mem (m.pa a).toNat 16 (wbyte v) ∧
      (∀ p, t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + 16
        then some (wbyte v (p - (m.pa a).toNat)) else s.mem[p]?) := by
  have hif := gpr_not_if hA.base.gpr
  rcases stp_lse2_strong a ha acc s v hA (m.pa a) (preW_of acc s hD hB hMTE2) hD.spe hLSE
      (fun u hu hum => by
        rcases hT u hu hum a acc true _ hp with
          ⟨ad, t, ht, hf, hpa, hmt, hin, hout, hv, _, hdata, hm, _⟩
        exact ⟨ad, t, ht, hf, hpa, hmt, hin, hout, hv, hdata hif, hm⟩) hio with
    ⟨u, ad, t1, t, fu, h1, h, hev, hr, hm, hget⟩
  rcases events_of hT a acc true _ hp u fu ad t1 h1 with ⟨ti, W, hev1, hW⟩
  exact ⟨ad, ti, W, t, h, by rw [hev, hev1, push_end], hW, hr, hm, hget⟩

#print axioms postRegs2_of
#print axioms preW_of
#print axioms postW_of
#print axioms e17s_of
#print axioms strongTA_of
#print axioms events_of
#print axioms push_end
#print axioms readV3_ldrb
#print axioms readV3_ldp_lse2
#print axioms strbV3
#print axioms stpV3_lse2
end MemM1.MemDataV3
