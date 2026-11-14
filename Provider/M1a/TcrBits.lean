import M1a.HostBits
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.TB
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality ArmCert.Eval.JointSAT ArmCert.Eval.JointSAT.EL20.Fields

/- TCR_EL2 as bit predicates (defects 4797,): the fields of TCR_EL2 the EL2&0
   lower-range Get actually reads, instead of the exact word EL20.tcr. -/

/-- The TCR_EL2 bits read for the lower range (values of the GB10 C34 word EL20.tcr). -/
structure TcrBits (tcr : BitVec 64) : Prop where
  t0sz : _get_TCR_EL2_Type_T0SZ tcr = 16#6
  tg0 : _get_TCR_EL2_Type_TG0 tcr = 0#2
  ips : _get_TCR_EL2_Type_IPS tcr = 5#3
  ds : BitVec.slice tcr 59 1 = 0#1
  ha : BitVec.slice tcr 39 1 = 1#1
  hd : BitVec.slice tcr 40 1 = 1#1
  nfd0 : Sail.BitVec.extractLsb tcr 53 53 = 0#1
  e0pd0 : Sail.BitVec.extractLsb tcr 55 55 = 0#1

theorem tcr_bits : TcrBits EL20.tcr := ⟨by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide⟩

theorem native_fields_tcr (tcr sctlr tcr2 hcr sctlr2 scr mair2 pir pire0 : BitVec 64)
    (ttbr0 ttbr1 : BitVec 128) (s : State) (hT : TcrBits tcr)
    (h47 : s.regs.FeatureImpl[47] = true)
    (hEE : _get_SCTLR_EL2_Type_EE sctlr = 0#1) (hWXN : _get_SCTLR_EL2_Type_WXN sctlr = 0#1)
    (htcr2 : s.regs.FeatureImpl[178] = true → tcr2 = 0#64) :
    Good s (S1ParamsHostLower.native tcr tcr2 hcr sctlr sctlr2 scr mair2 pir pire0
      ttbr0 ttbr1 s) := by
  obtain ⟨_, _, _, _, hha, hhd, hnfd, he0⟩ := hT
  observe_simp [Good, Fields, S1ParamsHostLower.native, Mk_MAIRType]
  refine ⟨?_, ?_⟩
  · by_cases h178 : s.regs.FeatureImpl[178] = true
    · have h0 := htcr2 h178
      subst h0
      have e5 : Sail.BitVec.extractLsb (0#64) 5 5 = 0#1 := by decide
      have e1 : Sail.BitVec.extractLsb (0#64) 1 1 = 0#1 := by decide
      simp only [e5, e1, ite_self]; decide
    · simp [h178]
  · intro _ h178
    have h0 := htcr2 h178
    subst h0
    intro _ _; decide

/-- EL20.Host with TCR_EL2 as bit predicates (MAIR_EL2 still the exact word: the walk
    package's Context fixes wp.mair). -/
structure HostT (s : State) : Prop where
  el3A64 : s.regs.FeatureImpl[7] = true
  noEL3A32 : s.regs.FeatureImpl[3] = false
  noRME : s.regs.FeatureImpl[232] = false
  a64 : s.regs.PSTATE.nRW = 0#1
  tcr : TcrBits (s.regs.bank_BitVec_64 .TCR_EL2)
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  /-- MEASURED-CONFIG PREMISE = ArmCert premise E2: MAIR_EL2 is the Linux compile-time
      MAIR_EL1_SET constant 0x000000040044ffff (GB10/C34 value: attr0 = attr1 = 0xff Normal WB,
      attr2 = 0x44 Normal NC, attr3 = 0x00 Device-nGnRnE, attr4 = 0x04 Device-nGnRE). Dependency
: attr1 = 0xff holds only while MTE is not enabled at runtime (cpu_enable_mte
      rewrites MT_NORMAL_TAGGED to 0xf0); GB10 hwcaps show no 'mte'. Generalizing the walk package
      over MAIR (attr bytes 0/1 only) is backlog 55. -/
  mair : s.regs.bank_BitVec_64 .MAIR_EL2 = 0x000000040044ffff#64
  tcr2 : s.regs.FeatureImpl[178] = true → s.regs.bank_BitVec_64 .TCR2_EL2 = 0#64

theorem HostT.of_regs {s t : State} (h : HostT s) (hr : t.regs = s.regs) : HostT t := by
  rcases h with ⟨a, b, c, d, e, f, g, i⟩
  exact ⟨by rw [hr]; exact a, by rw [hr]; exact b, by rw [hr]; exact c, by rw [hr]; exact d,
    by rw [hr]; exact e, by rw [hr]; exact f, by rw [hr]; exact g, by rw [hr]; exact i⟩

theorem Host.toT {s : State} (h : EL20.Host s) : HostT s :=
  ⟨h.el3A64, h.noEL3A32, h.noRME, h.a64, by rw [h.tcr]; exact tcr_bits, h.e2h, h.mair, h.tcr2⟩

/-- The actual public Get for EL2&0 at a lower VA under HostT (generic TCR). -/
theorem getT (va : BitVec 64) (s : State) (h : HostT s)
    (hvr : AArch64_GetVARange va = .VARange_LOWER) :
    ∃ wp t, AArch64_GetS1TTWParams .Regime_EL20 .SS_NonSecure va s = .ok wp t ∧
      Frame s t ∧ EL20.Active wp := by
  rw [EL20.get_eq]
  rcases GetGuestFields.Dispatch.prefix_normal s with ⟨ig, t, hp, hf⟩
  have ht : HostT t := h.of_regs hf.1
  have hz : ∀ f : BitVec 64 → BitVec 1, f 0#64 = 0#1 → t.regs.FeatureImpl[178] = true →
      f (t.regs.bank_BitVec_64 .TCR2_EL2) = 0#1 := by
    intro f hf0 h178; rw [ht.tcr2 h178]; exact hf0
  rcases S1ParamsHostLowerFacts.total (t.regs.bank_BitVec_64 .TCR_EL2)
    (t.regs.bank_BitVec_64 .TCR2_EL2)
    (t.regs.bank_BitVec_64 .HCR_EL2) (t.regs.bank_BitVec_64 .SCTLR_EL2)
    (t.regs.bank_BitVec_64 .SCTLR2_EL2) (t.regs.bank_BitVec_64 .SCR_EL3)
    (t.regs.bank_BitVec_64 .MAIR2_EL2) (t.regs.bank_BitVec_64 .PIR_EL2)
    (t.regs.bank_BitVec_64 .PIRE0_EL2) (t.regs.bank_BitVec_128 ._TTBR0_EL2)
    (t.regs.bank_BitVec_128 .TTBR1_EL2) t ht.el3A64 ht.noEL3A32 ht.noRME ht.a64 rfl
    rfl rfl rfl rfl rfl ht.mair rfl rfl rfl rfl rfl ht.tcr.tg0 ht.e2h
    (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) ht.tcr.ds with
    ⟨wp, u, hr, hfu, a, b, c, _, d, e, f, g⟩
  refine ⟨wp, u, ?_, ⟨hfu.1.trans hf.1, hfu.2.1.trans hf.2.1, hfu.2.2.trans hf.2.2⟩,
    a, b, c, d, e, by rw [f]; exact ht.tcr.t0sz, by rw [g]; exact ht.tcr.ips⟩
  rw [hvr]
  simp only [Bind.bind, EStateM.bind, hp, hr]

theorem get_fields_tcr (va : BitVec 64) (s : State) (h : HostT s)
    (h47 : s.regs.FeatureImpl[47] = true)
    (hEE : _get_SCTLR_EL2_Type_EE (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (hWXN : _get_SCTLR_EL2_Type_WXN (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (hvr : AArch64_GetVARange va = .VARange_LOWER) :
    ∀ wp t, AArch64_GetS1TTWParams .Regime_EL20 .SS_NonSecure va s = .ok wp t → Fields wp := by
  intro wp t hg
  rw [EL20.get_eq] at hg
  rcases GetGuestFields.Dispatch.prefix_normal s with ⟨ig, t1, hp, hf⟩
  have h1 : HostT t1 := h.of_regs hf.1
  have hz : ∀ f : BitVec 64 → BitVec 1, f 0#64 = 0#1 → t1.regs.FeatureImpl[178] = true →
      f (t1.regs.bank_BitVec_64 .TCR2_EL2) = 0#1 := by
    intro f hf0 h178; rw [h1.tcr2 h178]; exact hf0
  have hr := S1ParamsHostLower.complete (t1.regs.bank_BitVec_64 .TCR_EL2)
    (t1.regs.bank_BitVec_64 .TCR2_EL2)
    (t1.regs.bank_BitVec_64 .HCR_EL2) (t1.regs.bank_BitVec_64 .SCTLR_EL2)
    (t1.regs.bank_BitVec_64 .SCTLR2_EL2)
    (t1.regs.bank_BitVec_64 .SCR_EL3) (t1.regs.bank_BitVec_64 .MAIR2_EL2)
    (t1.regs.bank_BitVec_64 .PIR_EL2) (t1.regs.bank_BitVec_64 .PIRE0_EL2)
    (t1.regs.bank_BitVec_128 ._TTBR0_EL2) (t1.regs.bank_BitVec_128 .TTBR1_EL2) t1
    h1.el3A64 h1.noEL3A32 h1.noRME h1.a64 rfl rfl rfl rfl rfl rfl
    h1.mair rfl rfl rfl rfl rfl h1.tcr.tg0 h1.e2h
    (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) h1.tcr.ds
  have hstep : (GetGuestFields.Dispatch.initialDraw >>= fun _ =>
      AArch64_S1TTWParamsEL20 .SS_NonSecure (AArch64_GetVARange va)) s =
      AArch64_S1TTWParamsEL20 .SS_NonSecure (AArch64_GetVARange va) t1 := by
    simp only [Bind.bind, EStateM.bind, hp]
  rw [hstep, hvr, hr] at hg
  have hgood := native_fields_tcr (t1.regs.bank_BitVec_64 .TCR_EL2)
    (t1.regs.bank_BitVec_64 .SCTLR_EL2)
    (t1.regs.bank_BitVec_64 .TCR2_EL2) (t1.regs.bank_BitVec_64 .HCR_EL2)
    (t1.regs.bank_BitVec_64 .SCTLR2_EL2) (t1.regs.bank_BitVec_64 .SCR_EL3)
    (t1.regs.bank_BitVec_64 .MAIR2_EL2) (t1.regs.bank_BitVec_64 .PIR_EL2)
    (t1.regs.bank_BitVec_64 .PIRE0_EL2) (t1.regs.bank_BitVec_128 ._TTBR0_EL2)
    (t1.regs.bank_BitVec_128 .TTBR1_EL2) t1 h1.tcr (by rw [hf.1]; exact h47)
    (by rw [hf.1]; exact hEE) (by rw [hf.1]; exact hWXN) h1.tcr2
  rw [hg] at hgood
  exact hgood

#print axioms native_fields_tcr
#print axioms getT
#print axioms get_fields_tcr

/-- Host20 with TCR_EL2 and the feature vector / SCTLR as bit predicates; MAIR_EL2 is the
 labeled measured-config premise HostT.mair. -/
structure Host20T (s : State) : Prop where
  host : HostT s
  hafdbs : s.regs.FeatureImpl[47] = true
  ee : _get_SCTLR_EL2_Type_EE (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1
  wxn : _get_SCTLR_EL2_Type_WXN (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1
  pa : s.regs.bank_Int .__supported_pa_size = 48
  el0 : s.regs.PSTATE.EL = 0#2
  tlb : s.regs.bank_Bool .__tlb_enabled = false
  vm : _get_HCR_EL2_Type_VM (s.regs.bank_BitVec_64 .HCR_EL2) = 0#1
  dc : _get_HCR_EL2_Type_DC (s.regs.bank_BitVec_64 .HCR_EL2) = 0#1

theorem Host20T.of_regs {s t : State} (h : Host20T s) (hr : t.regs = s.regs) : Host20T t := by
  rcases h with ⟨a, b, c, d, e, f, g, i, j⟩
  exact ⟨a.of_regs hr, by rw [hr]; exact b, by rw [hr]; exact c, by rw [hr]; exact d,
    by rw [hr]; exact e, by rw [hr]; exact f, by rw [hr]; exact g, by rw [hr]; exact i,
    by rw [hr]; exact j⟩

theorem Host20B.toT {s : State} (h : ArmCert.Eval.M1a.HB.Host20B s) : Host20T s :=
  ⟨Host.toT h.host, h.hafdbs, h.ee, h.wxn, h.pa, h.el0, h.tlb, h.vm, h.dc⟩

open S1OuterSetup S1LogicalReference ArmCert.Eval.M1a ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv

theorem translate_walk_path_evT (s : State) (h : Host20T s) (va : BitVec 64)
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
  have ht : Host20T t := h.of_regs htr
  rw [hss]
  rcases getT va t ht.host hvr with ⟨wp, u, hg, hfr, htg, hd128, haie, hds, hmair, htx, hps⟩
  have hFw := get_fields_tcr va t ht.host ht.hafdbs ht.ee ht.wxn hvr wp u hg
  rcases hFw with ⟨hee, hwxn, hha, hhd, hpie, hrest⟩
  have hhaft : wp.haft = 0#1 := hrest.2.2
  refine ⟨wp, u, hg, hfr, ⟨hee, hwxn, hha, hhd, hpie, hrest⟩,
    ⟨htg, hd128, haie, hds, hmair, htx, hps⟩, ?_⟩
  intro v hvt hvm
  have hvs : v.regs = s.regs := hvt.trans htr
  have hvm' : v.mem = s.mem := hvm.trans htm
  have hv : Host20T v := h.of_regs hvs
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



theorem translate_walk_path_T (s : State) (h : Host20T s) (va : BitVec 64)
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
  (translate_walk_path_evT s h va hvr hEPD0 hRootIn observe available realizes identity htab
    slotL physL vL path D hD hleaf).walkFact

theorem Host20T.fetch {s t : State} (h : Host20T s)
    (ht : t.regs = ArmCert.Eval.M1a.Fetch2.fetchRegs s.regs) : Host20T t := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, b, c, d, e, f, g, i, j⟩ := h
  have hb : t.regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled := by
    rw [ht]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [ht]
  all_goals first
    | exact a1 | exact a2 | exact a3 | exact a4 | exact a5 | exact a6 | exact a7 | exact a8
    | exact b | exact c | exact d | exact e | exact f | exact i | exact j
    | (rw [← ht, hb]; exact g)


#print axioms Host20B.toT
#print axioms translate_walk_path_evT
#print axioms translate_walk_path_T
#print axioms Host20T.fetch
end ArmCert.Eval.M1a.TB
