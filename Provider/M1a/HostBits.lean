import M1a.WalkEvents
import M1a.Fetch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.HB
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality ArmCert.Eval.JointSAT ArmCert.Eval.JointSAT.EL20.Fields

/-- native_fields (joint Fields20) with the feature vector and SCTLR_EL2 word replaced by the
    bits the EL2&0 lower-range parameter computation actually reads for Fields:
    FEAT_HAFDBS (fv[47]), SCTLR_EL2.EE = WXN = 0, and FEAT_TCR2 → TCR2_EL2 = 0. -/
theorem native_fields_bits (sctlr tcr2 hcr sctlr2 scr mair2 pir pire0 : BitVec 64)
    (ttbr0 ttbr1 : BitVec 128) (s : State)
    (h47 : s.regs.FeatureImpl[47] = true)
    (hEE : _get_SCTLR_EL2_Type_EE sctlr = 0#1) (hWXN : _get_SCTLR_EL2_Type_WXN sctlr = 0#1)
    (htcr2 : s.regs.FeatureImpl[178] = true → tcr2 = 0#64) :
    Good s (S1ParamsHostLower.native EL20.tcr tcr2 hcr sctlr sctlr2 scr mair2 pir pire0
      ttbr0 ttbr1 s) := by
  observe_simp [Good, Fields, S1ParamsHostLower.native, Mk_MAIRType]
  refine ⟨by decide, by decide, ?_, fun _ => by decide, fun _ => by decide, ?_⟩
  · by_cases h178 : s.regs.FeatureImpl[178] = true
    · have h0 := htcr2 h178
      subst h0
      have e5 : Sail.BitVec.extractLsb (0#64) 5 5 = 0#1 := by decide
      have e1 : Sail.BitVec.extractLsb (0#64) 1 1 = 0#1 := by decide
      simp only [e5, e1, ite_self]; decide
    · simp [h178]
  · intro _ _ h178
    have h0 := htcr2 h178
    subst h0
    intro _ _; decide

/-- Host20 with bit predicates (defects e8cc): the joint EL20.Host register facts plus
    FEAT_HAFDBS, SCTLR_EL2.EE = WXN = 0, PA48, EL0, tlb off, HCR_EL2.VM = DC = 0. No full
    feature vector and no full SCTLR word. -/
structure Host20B (s : State) : Prop where
  host : EL20.Host s
  hafdbs : s.regs.FeatureImpl[47] = true
  ee : _get_SCTLR_EL2_Type_EE (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1
  wxn : _get_SCTLR_EL2_Type_WXN (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1
  pa : s.regs.bank_Int .__supported_pa_size = 48
  el0 : s.regs.PSTATE.EL = 0#2
  tlb : s.regs.bank_Bool .__tlb_enabled = false
  vm : _get_HCR_EL2_Type_VM (s.regs.bank_BitVec_64 .HCR_EL2) = 0#1
  dc : _get_HCR_EL2_Type_DC (s.regs.bank_BitVec_64 .HCR_EL2) = 0#1

theorem Host20B.of_regs {s t : State} (h : Host20B s) (hr : t.regs = s.regs) : Host20B t := by
  rcases h with ⟨a, b, c, d, e, f, g, i, j⟩
  exact ⟨a.of_regs hr, by rw [hr]; exact b, by rw [hr]; exact c, by rw [hr]; exact d,
    by rw [hr]; exact e, by rw [hr]; exact f, by rw [hr]; exact g, by rw [hr]; exact i,
    by rw [hr]; exact j⟩


theorem get_fields_bits (va : BitVec 64) (s : State) (h : Host20B s)
    (hvr : AArch64_GetVARange va = .VARange_LOWER) :
    ∀ wp t, AArch64_GetS1TTWParams .Regime_EL20 .SS_NonSecure va s = .ok wp t → Fields wp := by
  intro wp t hg
  rw [EL20.get_eq] at hg
  rcases GetGuestFields.Dispatch.prefix_normal s with ⟨ig, t1, hp, hf⟩
  have h1 : Host20B t1 := h.of_regs hf.1
  have hz : ∀ f : BitVec 64 → BitVec 1, f 0#64 = 0#1 → t1.regs.FeatureImpl[178] = true →
      f (t1.regs.bank_BitVec_64 .TCR2_EL2) = 0#1 := by
    intro f hf0 h178; rw [h1.host.tcr2 h178]; exact hf0
  have hr := S1ParamsHostLower.complete EL20.tcr (t1.regs.bank_BitVec_64 .TCR2_EL2)
    (t1.regs.bank_BitVec_64 .HCR_EL2) (t1.regs.bank_BitVec_64 .SCTLR_EL2)
    (t1.regs.bank_BitVec_64 .SCTLR2_EL2)
    (t1.regs.bank_BitVec_64 .SCR_EL3) (t1.regs.bank_BitVec_64 .MAIR2_EL2)
    (t1.regs.bank_BitVec_64 .PIR_EL2) (t1.regs.bank_BitVec_64 .PIRE0_EL2)
    (t1.regs.bank_BitVec_128 ._TTBR0_EL2) (t1.regs.bank_BitVec_128 .TTBR1_EL2) t1
    h1.host.el3A64 h1.host.noEL3A32 h1.host.noRME h1.host.a64 h1.host.tcr rfl rfl rfl rfl rfl
    h1.host.mair rfl rfl rfl rfl rfl
    (by decide) h1.host.e2h (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (by decide)
  have hstep : (GetGuestFields.Dispatch.initialDraw >>= fun _ =>
      AArch64_S1TTWParamsEL20 .SS_NonSecure (AArch64_GetVARange va)) s =
      AArch64_S1TTWParamsEL20 .SS_NonSecure (AArch64_GetVARange va) t1 := by
    simp only [Bind.bind, EStateM.bind, hp]
  rw [hstep, hvr, hr] at hg
  have hgood := native_fields_bits (t1.regs.bank_BitVec_64 .SCTLR_EL2)
    (t1.regs.bank_BitVec_64 .TCR2_EL2) (t1.regs.bank_BitVec_64 .HCR_EL2)
    (t1.regs.bank_BitVec_64 .SCTLR2_EL2) (t1.regs.bank_BitVec_64 .SCR_EL3)
    (t1.regs.bank_BitVec_64 .MAIR2_EL2) (t1.regs.bank_BitVec_64 .PIR_EL2)
    (t1.regs.bank_BitVec_64 .PIRE0_EL2) (t1.regs.bank_BitVec_128 ._TTBR0_EL2)
    (t1.regs.bank_BitVec_128 .TTBR1_EL2) t1 h1.hafdbs h1.ee h1.wxn h1.host.tcr2
  rw [hg] at hgood
  exact hgood

#print axioms native_fields_bits
#print axioms get_fields_bits
open S1OuterSetup S1LogicalReference ArmCert.Eval.M1a ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv

/-- translate_walk_path_ev on the bit-predicate host facts (defects e8cc). -/
theorem translate_walk_path_evB (s : State) (h : Host20B s) (va : BitVec 64)
    (hvr : AArch64_GetVARange va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hRootIn : (!is_zero_subrange (rootSlot s.regs va).address 55 48) = false)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe false false true true (fun a => s.mem[a]?))
    (identity : S1EntryPathSlots.Identity observe)
    (htab : ∀ l p v d, observe l p v → BytesAt false (fun a => s.mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d)
    (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64)
    (path : Path observe 48 va 0 9 ((rootOf s.regs va).setWidth 48) (.leaf 3 slotL physL vL))
    (D : BitVec 64) (hD : BytesAt false (fun a => s.mem[a]?) physL D)
    (hleaf : S1Contiguous.bit D = 0#1 ∧ BitVec.join1 [BitVec.access D 10] = 1#1 ∧
      ∀ v : TTWState, v.level = 3 → v.baseaddress.address = S1LeafBaseFrame.base D 3 →
        (!is_zero_subrange (S1StageOA.address va v).address 55 48) = false) :
    WalkFactE s va D := by
  intro t htr htm f acc' hf hss
  have ht : Host20B t := h.of_regs htr
  rw [hss]
  rcases ArmCert.Eval.JointSAT.EL20.get va t ht.host with ⟨wp, u, hg, hfr, htg, hd128, haie, hds, hmair, htx, hps⟩
  have hFw := get_fields_bits va t ht hvr wp u hg
  rcases hFw with ⟨hee, hwxn, hha, hhd, hpie, hrest⟩
  have hhaft : wp.haft = 0#1 := hrest.2.2
  refine ⟨wp, u, hg, hfr, ⟨hee, hwxn, hha, hhd, hpie, hrest⟩,
    ⟨htg, hd128, haie, hds, hmair, htx, hps⟩, ?_⟩
  intro v hvt hvm
  have hvs : v.regs = s.regs := hvt.trans htr
  have hvm' : v.mem = s.mem := hvm.trans htm
  have hv : Host20B v := h.of_regs hvs
  let cfg : S2Interface.Config :=
    ⟨v.regs.bank_BitVec_64 .HCR_EL2, v.regs.bank_BitVec_64 .VTCR_EL2,
     v.regs.bank_BitVec_64 .SCTLR_EL2, v.regs.bank_BitVec_64 .HCRX_EL2,
     v.regs.bank_BitVec_64 .S2PIR_EL2, v.regs.bank_BitVec_64 .SCR_EL3,
     v.regs.bank_BitVec_128 ._VTTBR_EL2, v.regs.bank_BitVec_64 .VTTBR⟩
  let c : Context :=
    { wp := wp, va := va, regime := .Regime_EL20, acc := acc', startlevel := 0,
      cfg := cfg, regimes := Or.inr rfl, d128 := hd128, ds := hds, tg := htg,
      aie := haie, mair := hmair, vm := hv.vm, dc := hv.dc, ss := hss }
  have hR : Ready c v :=
    ⟨hv.pa, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inl hv.el0, hv.host.noRME, hv.host.a64,
      hv.host.el3A64, hv.host.noEL3A32⟩
  have hpa : S2PhysicalSizeFrame.value c.wp.ps = 48 := by
    show S2PhysicalSizeFrame.value wp.ps = 48
    rw [hps]; decide
  have hbase : S1EntryRoot.base c.wp v.regs c.regime c.va = rootOf s.regs va := by
    show S1EntryRoot.base wp v.regs .Regime_EL20 va = _
    rw [base_eq wp v.regs va hd128 htg htx, hvs]
  have heeB : (c.wp.ee == 1#1) = false := by show (wp.ee == 1#1) = false; rw [hee]; decide
  have hpieB : (c.wp.pie == 1#1) = false := by show (wp.pie == 1#1) = false; rw [hpie]; decide
  have hhaB : (c.wp.ha == 1#1) = true := by show (wp.ha == 1#1) = true; rw [hha]; decide
  have hhdB : (c.wp.hd == 1#1) = true := by show (wp.hd == 1#1) = true; rw [hhd]; decide
  have hdec : ∀ x, S2FetchFrame.decoded c.wp.ee x = x := by
    intro x; simp [S2FetchFrame.decoded, show c.wp.ee = 0#1 from hee]
  have hmemv : (fun a : Nat => v.mem[a]?) = (fun a : Nat => s.mem[a]?) := by rw [hvm']
  rcases walk_result_path_ev c f v rfl hhaft hvr (by rw [hvs]; exact hEPD0) hR hf hv.tlb htx rfl
    (by
      show (!is_zero_subrange (S1EntryRoot.slot c.wp v.regs c.regime c.va).address 55
        (S2PhysicalSizeFrame.value c.wp.ps)) = false
      unfold S1EntryRoot.slot
      rw [hbase, hpa]; exact hRootIn)
    observe available (by rw [heeB, hpieB, hhaB, hhdB, hmemv]; exact realizes) identity
    (by rw [heeB, hmemv]; exact htab) slotL physL vL
    (by rw [hpa, hbase]; exact path)
    (by
      intro d hd
      rw [heeB, hmemv] at hd
      have hdD : d = D := bytes_unique _ _ _ _ hd hD
      subst hdD
      refine ⟨hleaf.1, hleaf.2.1, ?_⟩
      intro w hl hb
      rw [hpa]; exact hleaf.2.2 w hl hb) with ⟨D', r, w, hbytes, hw, hpost, W, hW, hWs, hRA⟩
  rw [heeB, hmemv, hdec] at hbytes
  have hDD : D' = D := bytes_unique _ _ _ _ hbytes hD
  subst hDD
  have hslot : S1EntryRoot.slot c.wp v.regs c.regime c.va = rootSlot s.regs va := by
    unfold S1EntryRoot.slot rootSlot; rw [hbase]
  rw [hslot] at hRA
  exact ⟨c, r, w, rfl, rfl, rfl, rfl, hw, hpost, W, hW, hWs, hRA⟩



theorem translate_walk_path_B (s : State) (h : Host20B s) (va : BitVec 64)
    (hvr : AArch64_GetVARange va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hRootIn : (!is_zero_subrange (rootSlot s.regs va).address 55 48) = false)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe false false true true (fun a => s.mem[a]?))
    (identity : S1EntryPathSlots.Identity observe)
    (htab : ∀ l p v d, observe l p v → BytesAt false (fun a => s.mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d)
    (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64)
    (path : Path observe 48 va 0 9 ((rootOf s.regs va).setWidth 48) (.leaf 3 slotL physL vL))
    (D : BitVec 64) (hD : BytesAt false (fun a => s.mem[a]?) physL D)
    (hleaf : S1Contiguous.bit D = 0#1 ∧ BitVec.join1 [BitVec.access D 10] = 1#1 ∧
      ∀ v : TTWState, v.level = 3 → v.baseaddress.address = S1LeafBaseFrame.base D 3 →
        (!is_zero_subrange (S1StageOA.address va v).address 55 48) = false) :
    WalkFact s va D :=
  (translate_walk_path_evB s h va hvr hEPD0 hRootIn observe available realizes identity htab
    slotL physL vL path D hD hleaf).walkFact

#print axioms translate_walk_path_evB
#print axioms translate_walk_path_B
/-- the fetch wrapper's own writes (BTypeCompatible, __InstructionStep) keep the
    host facts, so translate_walk_path_evB applies at the fetchRegs state of fetch_frame's MB. -/
theorem Host20B.fetch {s t : State} (h : Host20B s)
    (ht : t.regs = ArmCert.Eval.M1a.Fetch2.fetchRegs s.regs) : Host20B t := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, b, c, d, e, f, g, i, j⟩ := h
  have hb : t.regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled := by
    rw [ht]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [ht]
  all_goals first
    | exact a1 | exact a2 | exact a3 | exact a4 | exact a5 | exact a6 | exact a7 | exact a8
    | exact b | exact c | exact d | exact e | exact f | exact i | exact j
    | (rw [← ht, hb]; exact g)


end ArmCert.Eval.M1a.HB
