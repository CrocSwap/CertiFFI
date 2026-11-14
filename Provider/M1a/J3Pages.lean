import M1a.PagePath
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.J3P
abbrev State := SequentialState Regs oracleChoiceSource
open S1OuterSetup S1LogicalReference ArmCert.Eval.M1a ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv
open ArmCert.Eval.M1a.TB ArmCert.Eval.M1a.PP ArmCert.Eval.JointSAT

/- Concrete page walk facts on the J3c setup state:
   WalkFactE for EVERY VA of page 0 (J3b data leaf) and page 1 (J3c code leaf). -/

/-- The leaf output-address range check at va' (reads the page offset; memory's (a)). -/
def OAOk (va : BitVec 64) (D : BitVec 64) : Prop :=
  ∀ v : TTWState, v.level = 3 → v.baseaddress.address = S1LeafBaseFrame.base D 3 →
    (!is_zero_subrange (S1StageOA.address va v).address 55 48) = false

/-- translate_walk_path_evT with an exact-bytes Walk20 path from the root slot instead of a
    logical Path. -/
theorem walkFactE_of_walk20 (s : State) (h : Host20T s) (va : BitVec 64)
    (hvr : AArch64_GetVARange va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hRootIn : (!is_zero_subrange (rootSlot s.regs va).address 55 48) = false)
    (D : BitVec 64)
    (hwalk : ∀ wp : S1TTWParams, wp.ee = 0#1 → wp.ps = 5#3 →
      ∃ S, Walk20 wp va s.mem 4 0 (rootSlot s.regs va) 3 S D)
    (hc : S1Contiguous.bit D = 0#1) (haf : BitVec.join1 [BitVec.access D 10] = 1#1)
    (hoa : OAOk va D) : WalkFactE s va D := by
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
  have hslot : S1EntryRoot.slot c.wp v.regs c.regime c.va = rootSlot s.regs va := by
    unfold S1EntryRoot.slot rootSlot; rw [hbase]
  rcases hwalk wp hee hps with ⟨S, hW⟩
  have hW' : Walk20 c.wp c.va v.mem 4 0 (S1EntryRoot.slot c.wp v.regs c.regime c.va) 3 S D := by
    rw [hslot, hvm']; exact hW
  rcases walk_result_ev c f v 4 rfl hhaft hvr (by rw [hvs]; exact hEPD0) hR hf hv.tlb htx rfl
    (by
      show (!is_zero_subrange (S1EntryRoot.slot c.wp v.regs c.regime c.va).address 55
        (S2PhysicalSizeFrame.value c.wp.ps)) = false
      rw [hslot, hpa]; exact hRootIn)
    hW' rfl (by rw [hdec]; exact hc) (by rw [hdec]; exact haf)
    (by intro w hl hb; rw [hdec] at hb; rw [hpa]; exact hoa w hl hb) with
    ⟨r, w, hw, hpost, W, hWe, hRA⟩
  rw [hslot, hvm'] at hRA
  exact ⟨c, r, w, rfl, rfl, rfl, rfl, hw, hpost, W, hWe, hRA.size, by rw [hvm']; exact hRA⟩

open J3b in
theorem loadC_data (m : Std.ExtHashMap Nat (BitVec 8)) : ∀ a d, ((a = B1 ∧ d = d1) ∨
    (a = B2 ∧ d = d2) ∨ (a = B3 ∧ d = d3) ∨ (a = B4 ∧ d = J3b.leaf)) → ∀ i, i < 8 →
    (loadC m)[a + i]? = some (byte false d i) := by
  intro a d hs i hi
  unfold loadC
  rw [put_other _ _ _ _ (by rcases hs with ⟨rfl, _⟩|⟨rfl, _⟩|⟨rfl, _⟩|⟨rfl, _⟩ <;> simp only [B1, B2, B3, B4] <;> omega)]
  exact load_get m a d hs i hi



#print axioms walkFactE_of_walk20
#print axioms loadC_data
end ArmCert.Eval.M1a.J3P
